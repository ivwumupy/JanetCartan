module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Translation.Matrix
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Translation.PeriodicAlgebra
public import JanetCartan.Analysis.Fourier.Periodic.LocalL2
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Chart.Localization

/-!
# Translation inside the buffered periodic chart

The boundary argument for `app:ch_background:prop:bg-inverse`. A supported
output may be translated before or after periodization only when its translated
support remains in the representative cell. Source lifts agree on the buffered
source box, which is all the full two-position operator uses.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open JanetCartan.AmplitudeBound JanetCartan.PeriodicLocalL2
open JanetCartan.Pseudodifferential.DifferentialChart

namespace JanetCartan.ContinuumCommutator

variable {d : ℕ} {I : Type} [Fintype I]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℂ I
local notation "L²" => EuclideanL2 d V

/-- Quotient addition for the physical translations in
`app:ch_background:prop:bg-inverse`. -/
theorem torusQuotient_add_physical (x a : E) :
    torusQuotient (x + a) = torusQuotient x + torusQuotient a := by
  ext j
  exact AddCircle.coe_add 1 (x j) (a j)

/-- The coordinate shift uses the same positive sign on both spaces
(`app:ch_background:prop:bg-inverse`). -/
theorem torusQuotient_coordinateShift (i : Fin d) (h : ℝ) :
    torusQuotient (h • EuclideanSpace.single i 1) = periodicCoordinateShift i h := by
  classical
  ext j
  by_cases hij : i = j
  · subst j
    simp [torusQuotient, periodicCoordinateShift]
  · simp [torusQuotient, periodicCoordinateShift, EuclideanSpace.single, Ne.symm hij]

/-- The fixed enlarged box controls every translated source and output point
(`app:ch_background:prop:bg-inverse`). -/
theorem chartBox_add_coordinateShift_mem_cell {R h₀ h : ℝ}
    (hbuffer : R + h₀ < 1 / 2) (hsmall : |h| ≤ h₀)
    (i : Fin d) {x : E} (hx : x ∈ chartBox R) :
    x + h • EuclideanSpace.single i 1 ∈ halfOpenCell d := by
  apply subset_halfOpenCell_of_strict (K := chartBox (R + h₀))
    (fun y hy j ↦ (hy j).trans_lt hbuffer)
  intro j
  have ha : |(h • EuclideanSpace.single i (1 : ℝ)) j| ≤ h₀ := by
    by_cases hij : i = j
    · subst j
      simpa using hsmall
    · simpa [EuclideanSpace.single, Ne.symm hij] using
        (abs_nonneg h).trans hsmall
  exact (abs_add_le _ _).trans (add_le_add (hx j) ha)

omit [Fintype I] in
/-- Periodized chart cutoffs commute with translation when the translated
support stays in the cell. This proves the cell-boundary case rather than
assuming a global intertwining identity (`app:ch_background:prop:bg-inverse`). -/
theorem indicator_representative_add_of_supported_chart
    {K : Set E} (hcell : K ⊆ halfOpenCell d) (a : E)
    (hshift : ∀ x ∈ K, x - a ∈ halfOpenCell d) (f : E → V) (z : Torus d) :
    K.indicator f (centeredTorusRepresentative (z + torusQuotient a)) =
      K.indicator f (centeredTorusRepresentative z + a) := by
  let x := centeredTorusRepresentative z
  let y := centeredTorusRepresentative (z + torusQuotient a)
  have hqa : torusQuotient (-a) = -torusQuotient a := by
    ext j
    exact AddCircle.coe_neg _
  have hy : torusQuotient (y - a) = z := by
    rw [sub_eq_add_neg, torusQuotient_add_physical, hqa]
    simp [y]
  by_cases hxK : x + a ∈ K
  · have he : y = x + a := by
      have hc := centeredTorusRepresentative_quotient (hcell hxK)
      rw [torusQuotient_add_physical] at hc
      simpa [x, y] using hc
    change K.indicator f y = K.indicator f (x + a)
    rw [he]
  · have hyK : y ∉ K := by
      intro hyK
      have he := centeredTorusRepresentative_quotient (hshift y hyK)
      rw [hy] at he
      have he' : x + a = y := by
        change centeredTorusRepresentative z + a = y
        rw [he, sub_add_cancel]
      exact hxK (he' ▸ hyK)
    exact (indicator_of_notMem hyK f).trans (indicator_of_notMem hxK f).symm

/-- Supported vector L² outputs intertwine physical and periodic translation.
The explicit support margin is essential (`app:ch_background:prop:bg-inverse`). -/
theorem toTorus_vectorTranslation_of_supported
    {K : Set E} (hcell : K ⊆ halfOpenCell d) (a : E)
    (hshift : ∀ x ∈ K, x - a ∈ halfOpenCell d) (f : L²)
    (hf : ∀ᵐ x ∂volume, x ∉ K → f x = 0) :
    periodicL2Translation (torusQuotient a) (toTorus (𝕜 := ℂ) f) =
      toTorus (𝕜 := ℂ) (euclideanVectorL2Translation a f) := by
  have hfi : f =ᵐ[volume] K.indicator f := by
    filter_upwards [hf] with x hx
    by_cases h : x ∈ K
    · exact (indicator_of_mem h f).symm
    · simp [h, hx h]
  have hrep := (measurePreserving_representative (n := d)).quasiMeasurePreserving
  have htor := (measurePreserving_add_right (volume : Measure (Torus d))
    (torusQuotient a)).quasiMeasurePreserving
  have heuc := (measurePreserving_add_right (volume : Measure E) a).quasiMeasurePreserving
  apply Lp.ext
  filter_upwards [periodicL2Translation_coe (torusQuotient a) (toTorus (𝕜 := ℂ) f),
    htor.ae (toTorus_coe (𝕜 := ℂ) f),
    toTorus_coe (𝕜 := ℂ) (euclideanVectorL2Translation a f),
    hrep.ae_eq_comp (euclideanVectorL2Translation_coe a f).restrict,
    htor.ae (hrep.ae_eq_comp hfi.restrict),
    hrep.ae_eq_comp (heuc.ae_eq_comp hfi).restrict] with z ht hfz he hz h₁ h₂
  exact ht.trans (hfz.trans (h₁.trans
    ((indicator_representative_add_of_supported_chart hcell a hshift f z).trans
      (h₂.symm.trans (hz.symm.trans he.symm)))))

/-- The two translated source lifts agree on the buffered box. No global
commutation of zero extension with translation is asserted
(`app:ch_background:prop:bg-inverse`). -/
theorem toEuclidean_periodicTranslation_eq_on_chart
    {K : Set E} (hcell : K ⊆ halfOpenCell d) (a : E)
    (hshift : ∀ x ∈ K, x + a ∈ halfOpenCell d) (f : PeriodicL2 d V) :
    ∀ᵐ x ∂volume, x ∈ K →
      toEuclidean (𝕜 := ℂ) (periodicL2Translation (torusQuotient a) f) x =
        euclideanVectorL2Translation a (toEuclidean (𝕜 := ℂ) f) x := by
  have hq := (ae_restrict_iff' measurableSet_halfOpenCell).mp
    (measurePreserving_quotient.quasiMeasurePreserving.ae
      (periodicL2Translation_coe (torusQuotient a) f))
  filter_upwards [toEuclidean_coe (𝕜 := ℂ) (periodicL2Translation (torusQuotient a) f),
    euclideanVectorL2Translation_coe a (toEuclidean (𝕜 := ℂ) f),
    (measurePreserving_add_right (volume : Measure E) a).quasiMeasurePreserving.ae
      (toEuclidean_coe (𝕜 := ℂ) f), hq] with x hx he hs hq hxK
  rw [hx, indicator_of_mem (hcell hxK), he, hs, indicator_of_mem (hshift x hxK)]
  exact (hq (hcell hxK)).trans (congrArg f (torusQuotient_add_physical x a).symm)

end JanetCartan.ContinuumCommutator
