module

public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.Measure

/-!
# Exact integrals on a physical chart

The chart measure in `app:ch_background:defn:bg-row` is Euclidean Lebesgue
measure. Its quotient image has the restricted normalized Haar measure.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open JanetCartan.AmplitudeBound

namespace JanetCartan.PeriodicLocalL2
variable {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}

/-- The measurable torus chart selected by centered representatives
(`app:ch_background:defn:bg-row`). -/
def torusChart (K : Set (EuclideanSpace ℝ (Fin n))) : Set (Torus n) :=
  centeredTorusRepresentative ⁻¹' K

/-- For a physical chart inside the cell this is its actual quotient image
(`app:ch_background:defn:bg-row`). -/
theorem torusChart_eq_image (hcell : K ⊆ halfOpenCell n) :
    torusChart K = torusQuotient '' K := by
  ext z
  constructor
  · intro hz
    exact ⟨centeredTorusRepresentative z, hz, torusQuotient_centeredTorusRepresentative z⟩
  · rintro ⟨x, hx, rfl⟩
    change centeredTorusRepresentative (torusQuotient x) ∈ K
    rwa [centeredTorusRepresentative_quotient (hcell hx)]

/-- The quotient chart is measurable (`app:ch_background:defn:bg-row`). -/
theorem measurableSet_torusChart (hK : MeasurableSet K) : MeasurableSet (torusChart K) :=
  hK.preimage measurable_centeredTorusRepresentative

/-- Restricted Haar measure on the chart is exactly its Lebesgue measure
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem measurePreserving_chart_representative (hK : MeasurableSet K)
    (hcell : K ⊆ halfOpenCell n) :
    MeasurePreserving (centeredTorusRepresentative (n := n))
      (volume.restrict (torusChart K)) (volume.restrict K) := by
  have h := measurePreserving_representative.restrict_preimage hK
  rw [Measure.restrict_restrict_of_subset hcell] at h
  exact h

/-- Exact chart integral comparison (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem integral_chart_representative {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hK : MeasurableSet K) (hcell : K ⊆ halfOpenCell n)
    (f : EuclideanSpace ℝ (Fin n) → F) :
    (∫ z in torusChart K, f (centeredTorusRepresentative z)) = ∫ x in K, f x :=
  (measurePreserving_chart_representative hK hcell).integral_comp
    measurableEmbedding_representative f

/-- Chart-supported physical functions have exactly their Euclidean integral
on the auxiliary torus (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem integral_representative_of_supported {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (hcell : K ⊆ halfOpenCell n)
    (f : EuclideanSpace ℝ (Fin n) → F) (hf : ∀ x ∉ K, f x = 0) :
    (∫ z : Torus n, f (centeredTorusRepresentative z)) = ∫ x, f x := by
  rw [integral_representative]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦
    hf x (fun hk ↦ hx (hcell hk))

/-- The squared norm integral of a supported function has no extra factor
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem integral_norm_sq_representative_of_supported {F : Type*} [NormedAddCommGroup F]
    (hcell : K ⊆ halfOpenCell n) (f : EuclideanSpace ℝ (Fin n) → F)
    (hf : ∀ x ∉ K, f x = 0) :
    (∫ z : Torus n, ‖f (centeredTorusRepresentative z)‖ ^ 2) = ∫ x, ‖f x‖ ^ 2 := by
  exact integral_representative_of_supported hcell (fun x ↦ ‖f x‖ ^ 2)
    (fun x hx ↦ by simp [hf x hx])

end JanetCartan.PeriodicLocalL2
