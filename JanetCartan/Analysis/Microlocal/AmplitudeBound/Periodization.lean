module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Periodization.Derivatives

/-!
# Quantitative periodization of compact physical amplitudes

The fixed larger torus used in `app:ch_osc:lem:osc-amplitude`. For a uniformly
supported parameter family inside a centered box of radius less than `1/2`,
the construction preserves joint strong measurability, smoothness, and all
specified pure coordinate derivative bounds, with no loss in the constants.
The periodic lift agrees with the original amplitude on the whole closed cell.
Rescaling physical boxes to this cell is a separate step.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.AmplitudeBound

variable {n : ℕ} {X : Type*} [MeasurableSpace X]

/-- Strong measurability in the external parameter at every torus point
(`app:ch_osc:lem:osc-amplitude`). -/
theorem stronglyMeasurable_parameter_amplitudePeriodization
    {b : X → EuclideanSpace ℝ (Fin n) → ℂ}
    (hb : StronglyMeasurable (Function.uncurry b)) (z : Torus n) :
    StronglyMeasurable (fun ξ ↦ amplitudePeriodization (b ξ) z) :=
  (stronglyMeasurable_amplitudePeriodization hb).comp_measurable
    (measurable_id.prodMk measurable_const)

/-- Quantitative parameter-dependent periodization for
`app:ch_osc:lem:osc-amplitude`. All premises concern the original Euclidean
amplitude. The conclusions include exact closed-cell agreement and preservation
of every pure coordinate derivative bound through the prescribed order. -/
theorem amplitudePeriodization_spec {r : ℝ} (hr : r < 1 / 2)
    (b : X → EuclideanSpace ℝ (Fin n) → ℂ)
    (hm : StronglyMeasurable (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox r (b ξ))
    (hb : ∀ ξ, ContDiff ℝ ∞ (b ξ)) (N : ℕ) (A : ℝ)
    (hzero : ∀ ξ x, ‖b ξ x‖ ≤ A)
    (hderiv : ∀ ξ k, k ≤ N → ∀ i x,
      ‖euclideanCoordinateDerivList (List.replicate k i) (b ξ) x‖ ≤ A) :
    StronglyMeasurable (Function.uncurry (fun ξ ↦ amplitudePeriodization (b ξ))) ∧
    (∀ ξ, IsSmoothPeriodic (amplitudePeriodization (b ξ))) ∧
    (∀ ξ x, x ∈ fundamentalCell n →
      periodicLift (amplitudePeriodization (b ξ)) x = b ξ x) ∧
    (∀ ξ z, ‖amplitudePeriodization (b ξ) z‖ ≤ A) ∧
    (∀ ξ k, k ≤ N → ∀ i z,
      ‖periodicCoordinateDerivList (List.replicate k i) (amplitudePeriodization (b ξ)) z‖ ≤ A) := by
  exact ⟨stronglyMeasurable_amplitudePeriodization hm,
    fun ξ ↦ isSmoothPeriodic_amplitudePeriodization hr (hs ξ) (hb ξ),
    fun ξ _ hx ↦ periodicLift_amplitudePeriodization_eq hr (hs ξ) hx,
    fun ξ ↦ norm_amplitudePeriodization_le (hzero ξ),
    norm_pureDeriv_amplitudePeriodization_le hr hs hb N (fun _ ↦ A) hderiv⟩

end JanetCartan.AmplitudeBound
