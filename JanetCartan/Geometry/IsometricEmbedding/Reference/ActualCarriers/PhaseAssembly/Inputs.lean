module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.PhaseAssembly.Restriction
public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.Assembly

/-!
# Full-phase inputs for finite carrier assembly

These are conditional inputs to `exists_finite_carrierPhase_assembly`, not a
construction of the actual menu. `jc-hamilton-phase` produces the smooth full
charts, fixed domains and full momentum comparisons; `jc-frozen-carrier-menu`
provides the frozen patches and adapted sections; `jc-projected-stress-frame`
identifies the current symbol and controls its perturbation. No carrier phase,
carrier derivative estimate, chord bound or detector is an input field.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace Topology

namespace JanetCartan.ActualCarriers
open HamiltonPhase FrozenMenu

/-- Fixed reference full-phase data for one frozen patch in Steps 1–2 of
`app:ch_seed:prop:seed-actual-menu`. All coordinates are the shared Euclidean
spaces; the spatial projection is literally the adjoint of the section isometry.
The affine reference identity records the manuscript's positive sign. -/
structure CarrierPhaseReference {n : ℕ} (P : Patch n) where
  sectionEmbedding : Euclidean (n - 1) →ₗᵢ[ℝ] Euclidean n
  symbol : HomogeneousSymbol (Euclidean n)
  flow : HamiltonFlow symbol (Euclidean (n - 1))
  chart : ProjectionChart flow
  radius : ℝ
  radius_pos : 0 < radius
  momentum_smooth : ContDiffOn ℝ ∞ flow.momentum (flow.time ×ˢ flow.parameters)
  coordinates_smooth : ContDiffOn ℝ ∞ chart.coordinates chart.target
  covector : (ℝ × Euclidean (n - 1)) → Euclidean n
  phase_linear : ∀ q ∈ chart.target, phase chart.coordinates q = ⟪covector q.2, q.1⟫_ℝ
  patch_covector : ∀ z ∈ parameterInterior (2 * P.radius),
    covector (0, sectionEmbedding.toContinuousLinearMap.adjoint (P.toFun z)) = P.toFun z
  target_contains : ∀ x ∈ ball (0 : Euclidean n) radius,
    ∀ z ∈ parameterInterior (2 * P.radius),
      (x, (0, sectionEmbedding.toContinuousLinearMap.adjoint (P.toFun z))) ∈ chart.target

/-- The actual spatial projection `ζₐ` of the frozen patch
(`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
def CarrierPhaseReference.spatialPatch {n : ℕ} {P : Patch n}
    (R : CarrierPhaseReference P) : Euclidean 3 → Euclidean (n - 1) :=
  fun z ↦ R.sectionEmbedding.toContinuousLinearMap.adjoint (P.toFun z)

/-- Primitive full-phase production/comparison output on the fixed reference
target (`app:lem:common-hamilton-phase`). In particular the estimates are for
full momentum and its full derivative, before any patch restriction. Uniform
production of this record is a separate analytic obligation. -/
structure CarrierFullPhaseInput {n : ℕ} {P : Patch n} (R : CarrierPhaseReference P)
    (H : HomogeneousSymbol (Euclidean n)) (bound : ℝ) where
  flow : HamiltonFlow H (Euclidean (n - 1))
  chart : ProjectionChart flow
  target_eq : chart.target = R.chart.target
  section_eq : flow.sectionMap = R.sectionEmbedding.toContinuousLinearMap
  momentum_smooth : ContDiffOn ℝ ∞ flow.momentum (flow.time ×ˢ flow.parameters)
  coordinates_smooth : ContDiffOn ℝ ∞ chart.coordinates chart.target
  section_source : ∀ u, R.sectionEmbedding u ∈ ball (0 : Euclidean n) R.radius →
    ∀ z ∈ parameterInterior (2 * P.radius), (0, (u, (0, R.spatialPatch z))) ∈ chart.source
  comparison : ∀ q ∈ R.chart.target,
    ‖chart.chartMomentum q - R.chart.chartMomentum q‖ ≤ bound ∧
    ‖fderiv ℝ chart.chartMomentum q - fderiv ℝ R.chart.chartMomentum q‖ ≤ bound

/-- Smoothness of the literal projected frozen patch
(`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem CarrierPhaseReference.spatialPatch_smooth {n : ℕ} {P : Patch n}
    (R : CarrierPhaseReference P) {c C : ℝ} (hP : P.IsValid c C) :
    ContDiffOn ℝ ∞ R.spatialPatch (parameterInterior (2 * P.radius)) :=
  R.sectionEmbedding.toContinuousLinearMap.adjoint.contDiff.comp_contDiffOn hP.2.2.2.1

/-- On the whole open patch neighborhood, the reference carrier gradient is
the frozen patch covector, with the same section sign
(`app:ch_seed:prop:seed-actual-menu`, Steps 1–2). -/
theorem CarrierPhaseReference.frozen_gradient {n : ℕ} {P : Patch n}
    (R : CarrierPhaseReference P) {x : Euclidean n} {z : Euclidean 3}
    (hx : x ∈ ball (0 : Euclidean n) R.radius)
    (hz : z ∈ parameterInterior (2 * P.radius)) :
    gradient (fun y ↦ carrierPhase R.chart R.spatialPatch y z) x = P.toFun z := by
  rw [(hasGradientAt_carrierPhase R.chart R.spatialPatch (R.target_contains x hx z hz)).gradient]
  exact (chartMomentum_eq_of_phase_linear R.chart R.covector R.phase_linear
    (R.target_contains x hx z hz)).trans (R.patch_covector z hz)

/-- The frozen derivative bound used by finite phase assembly is obtained from
compactness, not imposed as an extra analytic input
(`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem CarrierPhaseReference.exists_patch_derivative_bound {n : ℕ} {P : Patch n}
    (R : CarrierPhaseReference P) {c C : ℝ} (hP : P.IsValid c C) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ z ∈ parameterCube P.radius,
      ‖fderiv ℝ R.spatialPatch z‖ ≤ L ∧ ‖fderiv ℝ P.toFun z‖ ≤ L := by
  have hsub := parameterCube_subset_doubledInterior hP.1
  have h₁ := ((R.spatialPatch_smooth hP).continuousOn_fderiv_of_isOpen
    (isOpen_parameterInterior _) (by simp)).norm.mono hsub
  have h₂ := (hP.2.2.2.1.continuousOn_fderiv_of_isOpen
    (isOpen_parameterInterior _) (by simp)).norm.mono hsub
  obtain ⟨z, _, hz⟩ := (isCompact_parameterCube P.radius).exists_isMaxOn
    ⟨0, zero_mem_parameterCube hP.1.le⟩ (h₁.add h₂)
  refine ⟨max 1 (‖fderiv ℝ R.spatialPatch z‖ + ‖fderiv ℝ P.toFun z‖),
    le_max_left _ _, ?_⟩
  intro w hw
  have hb := (hz hw).trans (le_max_right 1 _)
  exact ⟨(le_add_of_nonneg_right (norm_nonneg _)).trans hb,
    (le_add_of_nonneg_left (norm_nonneg _)).trans hb⟩

end JanetCartan.ActualCarriers
