module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.PhaseAssembly.Inputs

/-!
# Comparison after frozen-patch restriction

Transfers the primitive full-phase comparison to the exact carrier gradient and
its parameter derivative (`app:ch_seed:prop:seed-actual-menu`, Step 2).
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff InnerProductSpace Topology
namespace JanetCartan.ActualCarriers
open HamiltonPhase FrozenMenu

/-- The reference gradient identity also identifies its parameter derivative,
since the identity holds on an open neighborhood of the closed parameter cube
(`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem CarrierPhaseReference.frozen_gradient_derivative {n : ℕ} {P : Patch n}
    (R : CarrierPhaseReference P) {x : Euclidean n} {z : Euclidean 3}
    (hx : x ∈ ball (0 : Euclidean n) R.radius)
    (hz : z ∈ parameterInterior (2 * P.radius)) :
    fderiv ℝ (fun w ↦ gradient (fun y ↦ carrierPhase R.chart R.spatialPatch y w) x) z =
      fderiv ℝ P.toFun z := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [(isOpen_parameterInterior _).mem_nhds hz] with w hw
  exact R.frozen_gradient hx hw

/-- Both required `C_z^1 C_x^0` comparisons follow from full chart-momentum
comparison; the derivative factor is the fixed projected frozen patch
(`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem CarrierFullPhaseInput.carrier_comparison {n : ℕ} {P : Patch n}
    {R : CarrierPhaseReference P} {H : HomogeneousSymbol (Euclidean n)} {bound : ℝ}
    (F : CarrierFullPhaseInput R H bound) (hbound : 0 ≤ bound)
    {c C : ℝ} (hP : P.IsValid c C) {x : Euclidean n} {z : Euclidean 3}
    (hx : x ∈ ball (0 : Euclidean n) R.radius) (hz : z ∈ parameterCube P.radius) :
    ‖gradient (fun y ↦ carrierPhase F.chart R.spatialPatch y z) x - P.toFun z‖ ≤ bound ∧
    ‖fderiv ℝ (fun w ↦ gradient (fun y ↦ carrierPhase F.chart R.spatialPatch y w) x) z -
      fderiv ℝ P.toFun z‖ ≤ bound * ‖fderiv ℝ R.spatialPatch z‖ := by
  have hz' := parameterCube_subset_doubledInterior hP.1 hz
  have ht₀ := R.target_contains x hx z hz'
  have ht : (x, (0, R.spatialPatch z)) ∈ F.chart.target := F.target_eq ▸ ht₀
  have hζ := ((R.spatialPatch_smooth hP).contDiffAt
    ((isOpen_parameterInterior _).mem_nhds hz')).differentiableAt (by simp)
  constructor
  · rw [(hasGradientAt_carrierPhase F.chart R.spatialPatch ht).gradient]
    have he := (chartMomentum_eq_of_phase_linear R.chart R.covector R.phase_linear ht₀).trans
      (R.patch_covector z hz')
    rw [← he]
    exact (F.comparison _ ht₀).1
  · rw [← R.frozen_gradient_derivative hx hz']
    exact norm_carrierGradient_parameter_sub_le F.chart R.chart
      F.momentum_smooth F.coordinates_smooth R.momentum_smooth R.coordinates_smooth
      hζ ht ht₀ hbound (F.comparison _ ht₀).2

/-- The section value is inherited from the same full Hamilton chart, so no
sign change is introduced by restricting to zero energy
(`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem CarrierFullPhaseInput.carrier_section {n : ℕ} {P : Patch n}
    {R : CarrierPhaseReference P} {H : HomogeneousSymbol (Euclidean n)} {bound : ℝ}
    (F : CarrierFullPhaseInput R H bound) {u : Euclidean (n - 1)} {z : Euclidean 3}
    (hu : R.sectionEmbedding u ∈ ball (0 : Euclidean n) R.radius)
    (hz : z ∈ parameterInterior (2 * P.radius)) :
    carrierPhase F.chart R.spatialPatch (R.sectionEmbedding u) z = ⟪u, R.spatialPatch z⟫_ℝ := by
  simpa only [carrierPhase, F.section_eq, LinearIsometry.coe_toContinuousLinearMap] using
    F.chart.initial_value (F.section_source u hu z hz)

end JanetCartan.ActualCarriers
