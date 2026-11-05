module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.PhysicalBounds

/-!
# Literal physical jets of compact Fourier integrals

For `app:ch_waves:eq:individual-raw-slice`, local compactness supplies the
integrable domination needed to differentiate the original Fourier density.
The consumer is the cutoff raw slice's weak-jet construction. No quantitative
frequency estimate is inferred from these local compactness bounds.
-/

@[expose] public noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace JanetCartan.RawPrimary

variable {X P F : Type}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [MeasurableSpace P] [BorelSpace P]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Every physical derivative commutes with the compact Fourier integral,
from joint smoothness and the original integrable density alone. This supplies
the literal jets in `app:ch_waves:eq:individual-raw-slice`. -/
theorem iteratedFDeriv_weightedCompactIntegral
    {U : Set X} {V T : Set P} (hU : IsOpen U) (hV : IsOpen V)
    (hT : IsCompact T) (hTV : T ⊆ V) {μ : Measure P}
    [IsFiniteMeasure (μ.restrict T)] {f : P → ℂ} (hf : IntegrableOn f T μ)
    {B : X × P → F} (hB : ContDiffOn ℝ ∞ B (U ×ˢ V))
    (j : ℕ) {x : X} (hx : x ∈ U) :
    iteratedFDeriv ℝ j (fun y ↦ ∫ η in T, f η • B (y, η) ∂μ) x =
      ∫ η in T, f η • iteratedFDeriv ℝ j (fun y ↦ B (y, η)) x ∂μ := by
  let : ProperSpace X := FiniteDimensional.proper_rclike ℝ X
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  have hbounds (k : ℕ) : ∃ C : ℝ, ∀ y ∈ Metric.closedBall x r, ∀ η ∈ T,
      ‖iteratedFDeriv ℝ k (fun z ↦ B (z, η)) y‖ ≤ C := by
    obtain ⟨C, hC⟩ := ((isCompact_closedBall x r).prod hT).exists_bound_of_continuousOn
      ((contDiffOn_atomPhysicalJet hU hV hB k).continuousOn.mono
        (Set.prod_mono hrU hTV))
    exact ⟨C, fun y hy η hη ↦ hC (y, η) ⟨hy, hη⟩⟩
  choose C hC using hbounds
  apply MeasureEnvelopes.iteratedFDeriv_synthesis (s := Metric.ball x r)
    (r := j) (C := C) Metric.isOpen_ball hf
  · filter_upwards [ae_restrict_mem hT.measurableSet] with η hη y hy
    have hyU := hrU (Metric.ball_subset_closedBall hy)
    exact ((hB.contDiffAt ((hU.prod hV).mem_nhds
      (show (y, η) ∈ U ×ˢ V from ⟨hyU, hTV hη⟩))).comp y
        (contDiffAt_id.prodMk contDiffAt_const)).of_le (by simp)
  · intro k _ y hy
    exact (integrableOn_compactParameter hT hTV
      (contDiffOn_atomPhysicalJet hU hV hB k).continuousOn
      (hrU (Metric.ball_subset_closedBall hy))).aestronglyMeasurable
  · intro k _
    filter_upwards [ae_restrict_mem hT.measurableSet] with η hη y hy
    exact hC k y (Metric.ball_subset_closedBall hy) η hη
  · exact le_rfl
  · exact Metric.mem_ball_self hr

end JanetCartan.RawPrimary
