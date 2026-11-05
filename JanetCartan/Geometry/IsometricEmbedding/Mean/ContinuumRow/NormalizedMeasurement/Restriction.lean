module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedMeasurement.Geometry

/-!
# Carry the supplied carriers into the fixed measurement chart

All statements concern the supplied data and operators. In particular there is
no second existential row, and the initial-variable measure is unchanged.
The literal realization premises are produced by `RetainedFrozen.Row` (or by
its retained local carrier producer); they are not coercivity/inverse premises.
The normalized selector uses this leaf with its original incidence index type.

Sources: `bg-T`, `bg-realification`, `bg-uniform-normalized`, and paper-v2.tex
`new:sec:order-of-choices`.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace JanetCartan.ContinuumRow.NormalizedMeasurement
open CommonMeasurement PeriodicLocalL2 AmplitudeBound

variable {n N : ℕ}

/-- Transfer the supplied carrier, with its full original angular support,
to the fixed common chart. The transport, covector, normal (including its
initial scalar) and stress frame are unchanged. The test and adjoint formulas
retain `carrierMeasure n` and identify the SAME restricted operator
(`bg-T`, `bg-realification`, `bg-uniform-normalized`). -/
theorem supplied_carrier_common_measurement (d : CarrierData n N)
    {r a' : ℝ} (hr : 0 < r) (ha' : 0 < a')
    (hcell : 4 * r < 1 / 2) (hlocal : 4 * a' < 1 / 2) (hra : 6 * r < a')
    (hchart : d.outputChart = torusChart (closedBall 0 (4 * a')))
    (hpoint : ∀ x ∈ d.outputChart, d.chartPoint x = centeredTorusRepresentative x)
    (hmeas : d.measurementCutoff = FixedCutoffs.periodic ha' hlocal 1) :
    let χ := FixedCutoffs.periodic (n := n) hr hcell 1
    let e := commonChartData d (closedBall 0 (4 * r)) χ
    e.angularCutoff = d.angularCutoff ∧ e.highCutoff = d.highCutoff ∧
    tsupport (Function.uncurry e.angularCutoff) = tsupport (Function.uncurry d.angularCutoff) ∧
    e.transportedPosition = d.transportedPosition ∧ e.covector = d.covector ∧
    e.normalField = d.normalField ∧ e.stressFrame = d.stressFrame ∧
    (∀ x u, carrierKernel e x u = χ x • carrierKernel d x u) ∧
    ∀ V : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
      ‖restrictCarrier χ V‖ ≤ ‖V‖ ∧
      ((∀ v : carrierInitialTestSpace n,
        V (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral d v.val) →
      (∀ v : carrierInitialTestSpace n,
        restrictCarrier χ V (carrierInitialTestToLp v) =ᵐ[volume]
          carrierTestIntegral e v.val) ∧
      (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ e.outputChart → restrictCarrier χ V f x = 0)) ∧
      ((∀ w : ComplexOutputL2 n,
          MemLp (carrierAdjointIntegral d w) 2 (carrierMeasure n) ∧
          V.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w) →
        ∀ w : ComplexOutputL2 n,
          MemLp (carrierAdjointIntegral e w) 2 (carrierMeasure n) ∧
          (restrictCarrier χ V).adjoint w =ᵐ[carrierMeasure n]
            carrierAdjointIntegral e w) := by
  intro χ e
  have hs : ∀ x, χ x ≠ 0 → x ∈ torusChart (closedBall 0 (4 * r)) :=
    fun _ hx ↦ fixed_measurement_mem_chart hr hcell hx
  have hK : torusChart (closedBall 0 (4 * r)) ⊆ d.outputChart := by
    rw [hchart]
    exact fun _ hx ↦ closedBall_subset_closedBall (by linarith : 4 * r ≤ 4 * a') hx
  have hp : ∀ x, χ x ≠ 0 → d.measurementCutoff x = 1 := by
    intro x hx
    rw [hmeas]
    exact (mul_eq_left₀ hx).mp
      (physical_measurement_mul hr ha' (by linarith : 3 * r ≤ 2 * a')
        (centeredTorusRepresentative x))
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro x u
    rw [← carrierKernel_fixed_common_chart d hr ha' hcell hlocal hra hchart hpoint hmeas]
    exact carrierKernel_restrictData d χ x u
  · intro V
    refine ⟨(restrictCarrier_norm_le χ V).trans ?_, ?_,
      fun hadj ↦ restrictCarrier_adjoint_common_chart d χ _ hs hK hpoint hp V hadj⟩
    · simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (FixedCutoffs.periodic_norm_le_one hr hcell 1) (norm_nonneg V)
    · intro hV
      have ht := restrictCarrier_test_common_chart d χ _ hs hK hpoint hp V hV
      exact ⟨ht, carrierRealization_eq_zero_outside _ _ ht⟩

end JanetCartan.ContinuumRow.NormalizedMeasurement
