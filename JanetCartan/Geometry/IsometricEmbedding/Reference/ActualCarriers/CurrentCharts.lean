module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.FrozenPhaseReference
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.NormalizedSymbolBounds

/-!
# Current Hamilton charts from primitive frame closeness

The first construction in `app:ch_seed:prop:seed-actual-menu` is instantiated
with the literal normalized determinant. The retained frozen state ball
supplies the annulus needed by the symbol-continuity theorem. The output uses
the retained perturbation family, so its section and target are the same as
the frozen reference's. No current flow, chart, scalar-symbol estimate or
carrier identity is an input.

This closes the local smooth construction, including the zero-section source
condition. Full momentum comparison and uniform higher estimates are still
needed for `CarrierFullPhaseInput`. The physical construction domain must
contain the retained state domain's physical projection. The construction in
`PhysicalReference` supplies a finite family fitting any prescribed positive
physical ball.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers
open HamiltonPhase FrozenMenu FrozenPhaseReference

/-- Primitive `C⁶` frame closeness produces current charts for the literal
normalized determinant on the same target as the decorated frozen chart.
The positive threshold precedes the current frame and all its higher norms.
The extra requested tolerance controls the scalar `C⁶` comparison used later
for phase continuity (`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem FrozenPhaseReference.FrozenPatchData.exists_current_chart_of_frame_closeness {n : ℕ}
    {P : Patch n} (d : FrozenPatchData P) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ (U : Set (Euclidean n)) (hU : IsOpen U),
      (∀ q ∈ d.localReference.stateDomain, q.1 ∈ U) →
      ∀ (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q U),
      cNorm (closedBall (0 : Euclidean n) d.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < δ →
      let H := normalizedHomogeneousSymbol hU Q hQ
      ∃ (Φ : HamiltonFlow H (Euclidean (n - 1))) (χ : ProjectionChart Φ),
        BufferedChartControl d.adapted.embedding d.adapted.baseData
          (transverseSectionState d.adapted.embedding d.adapted.normal
            (d.adapted.baseData, ⟪d.adapted.normal, d.center⟫_ℝ))
          d.localReference.stateRadius d.localReference.family.sourceRadius
          d.localReference.family.buffer d.localReference.family.coefficient
          d.localReference.family.target d.localReference.family.equivalence
          d.reference.flow Φ χ ∧
        χ.target = d.reference.chart.target ∧
        (∀ u, d.reference.sectionEmbedding u ∈ ball 0 d.reference.radius →
          ∀ z ∈ parameterCube (2 * P.radius),
            (0, (u, (0, d.reference.spatialPatch z))) ∈ χ.source) ∧
        cNorm (closedBall (0, d.center) d.localReference.stateRadius) 6
          (fun q ↦ H.h q - d.reference.symbol.h q) < η := by
  have hball : closedBall (0, d.center) d.localReference.stateRadius ⊆
      d.localReference.stateDomain := by
    simpa only [d.adapted.baseState_eq] using d.localReference.stateBall_subset
  have hzero (ξ) (hξ : ξ ∈ closedBall d.center d.localReference.stateRadius) : ξ ≠ 0 := by
    apply (mem_frozenSymbol_domain (0, ξ)).mp
    apply d.localReference.state_subset
    apply hball
    simpa only [mem_closedBall, Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)] using hξ
  obtain ⟨δ, hδ, hsmall⟩ := NormalizedSymbolBounds.exists_cube_symbol_C3_C6_comparison_radius
    (0, d.center) d.localReference.stateRadius_pos hzero
    d.localReference.family.threshold_pos hη
  refine ⟨δ, hδ, ?_⟩
  intro U hU hdomain Q hQ hclose
  let H := normalizedHomogeneousSymbol hU Q hQ
  have hphysical : closedBall (0 : Euclidean n) d.localReference.stateRadius ⊆ U := by
    intro x hx
    apply hdomain (x, d.center)
    apply hball
    simpa only [mem_closedBall, Prod.dist_eq, dist_self, max_eq_left (dist_nonneg)] using hx
  have hs := hsmall U hU hphysical Q hQ hclose
  have hdom : d.localReference.stateDomain ⊆ H.domain := by
    intro q hq
    exact ⟨hdomain q hq, (mem_frozenSymbol_domain q).mp (d.localReference.state_subset hq)⟩
  have hsm : ContDiffOn ℝ ∞ H.h d.localReference.stateDomain :=
    (contDiffOn_normalizedSymbol hU hQ).mono hdom
  have hs₃ : cNorm (closedBall
      (transverseSectionState d.adapted.embedding d.adapted.normal
        (d.adapted.baseData, ⟪d.adapted.normal, d.center⟫_ℝ))
      d.localReference.stateRadius) 3 (fun q ↦ H.h q - d.reference.symbol.h q) ≤
        d.localReference.family.threshold := by
    rw [d.adapted.baseState_eq]
    exact hs.1.le
  obtain ⟨Φ, χ, ht, _, hc⟩ := d.exists_reference_perturbation H hdom hsm hs₃
  refine ⟨Φ, χ, hc, ht, ?_, hs.2⟩
  intro u hu z hz
  have href := d.reference_section_source hu hz
  change (0, (u, (0, d.reference.spatialPatch z))) ∈ d.localReference.family.chart.source at href
  rw [d.localReference.family.reference_control.source_eq] at href
  have hadm := hc.source_admissible (subset_closure href.1)
  rw [hc.source_eq]
  refine ⟨href.1, ?_⟩
  change (Φ.position (0, (u, (0, d.reference.spatialPatch z))),
    (0, d.reference.spatialPatch z)) ∈ d.localReference.family.target
  rw [Φ.initial_position _ hadm.2, hc.section_eq]
  exact hc.target_eq ▸ ht.symm ▸ d.reference_target_contains_closed hu hz

/-- Every chart just constructed gives the literal smooth zero-energy carrier,
its smooth gradient, exact characteristic equation and positive section sign.
The chart-control premise is the actual output of
`FrozenPatchData.exists_current_chart_of_frame_closeness`; this deduction does
not require a phase comparison or postulate a carrier
(`app:ch_seed:prop:seed-actual-menu`, Steps 1–2). -/
theorem FrozenPhaseReference.FrozenPatchData.current_carrier_identities {n : ℕ} {P : Patch n}
    (d : FrozenPatchData P) {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q U)
    {Φ : HamiltonFlow (normalizedHomogeneousSymbol hU Q hQ) (Euclidean (n - 1))}
    (χ : ProjectionChart Φ)
    (ht : χ.target = d.reference.chart.target)
    (hj : Φ.sectionMap = d.reference.sectionEmbedding.toContinuousLinearMap)
    (hm : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hχ : ContDiffOn ℝ ∞ χ.coordinates χ.target)
    (hsource : ∀ u, d.reference.sectionEmbedding u ∈ ball 0 d.reference.radius →
      ∀ z ∈ parameterCube (2 * P.radius), (0, (u, (0, d.reference.spatialPatch z))) ∈ χ.source) :
    ContDiffOn ℝ ∞ (fun q : Euclidean n × Euclidean 3 ↦
      carrierPhase χ d.reference.spatialPatch q.1 q.2)
      (ball 0 d.reference.radius ×ˢ parameterInterior (2 * P.radius)) ∧
    ContDiffOn ℝ ∞ (fun q : Euclidean n × Euclidean 3 ↦
      gradient (fun y ↦ carrierPhase χ d.reference.spatialPatch y q.2) q.1)
      (ball 0 d.reference.radius ×ˢ parameterInterior (2 * P.radius)) ∧
    (∀ x ∈ ball 0 d.reference.radius, ∀ z ∈ parameterCube (2 * P.radius),
      determinant (Q x) (gradient (fun y ↦ carrierPhase χ d.reference.spatialPatch y z) x) = 0) ∧
    (∀ u, d.reference.sectionEmbedding u ∈ ball 0 d.reference.radius →
      ∀ z ∈ parameterCube (2 * P.radius),
        carrierPhase χ d.reference.spatialPatch (d.reference.sectionEmbedding u) z =
          ⟪u, d.reference.spatialPatch z⟫_ℝ) := by
  have htarget (x) (hx : x ∈ ball 0 d.reference.radius)
      (z) (hz : z ∈ parameterInterior (2 * P.radius)) :
      (x, (0, d.reference.spatialPatch z)) ∈ χ.target :=
    ht.symm ▸ d.reference.target_contains x hx z hz
  refine ⟨contDiffOn_carrierPhase χ hχ (d.reference.spatialPatch_smooth hP) htarget,
    contDiffOn_carrierGradient χ hm hχ (d.reference.spatialPatch_smooth hP) htarget,
    ?_, ?_⟩
  · intro x hx z hz
    exact carrierPhase_normalizedSymbol_determinant_eq_zero hU Q hQ χ _
      (ht.symm ▸ d.reference_target_contains_closed hx hz)
  · intro u hu z hz
    simpa only [carrierPhase, hj, LinearIsometry.coe_toContinuousLinearMap] using
      χ.initial_value (hsource u hu z hz)

/-- Construct actual smooth characteristic carriers from the primitive frame
neighborhood, with the reference section and positive sign. This instantiates
both the Hamilton chart producer and its restriction theorem. No current phase,
flow, characteristic equation or section identity is an assumption
(`app:ch_seed:prop:seed-actual-menu`, Step 1). Quantitative comparison, rank,
signed-pair and root conclusions remain to be assembled separately. -/
theorem FrozenPhaseReference.FrozenPatchData.exists_current_carrier_of_frame_closeness {n : ℕ}
    {P : Patch n} (d : FrozenPatchData P) {c C : ℝ} (hP : P.IsValid c C) :
    ∃ δ > 0, ∀ (U : Set (Euclidean n)) (hU : IsOpen U),
      (∀ q ∈ d.localReference.stateDomain, q.1 ∈ U) →
      ∀ (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q U),
      cNorm (closedBall (0 : Euclidean n) d.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < δ →
      ∃ (Φ : HamiltonFlow (normalizedHomogeneousSymbol hU Q hQ) (Euclidean (n - 1)))
        (χ : ProjectionChart Φ) (Θ : Euclidean n → Euclidean 3 → ℝ),
        χ.target = d.reference.chart.target ∧
        Θ = carrierPhase χ d.reference.spatialPatch ∧
        ContDiffOn ℝ ∞ (fun q : Euclidean n × Euclidean 3 ↦ Θ q.1 q.2)
          (ball 0 d.reference.radius ×ˢ parameterInterior (2 * P.radius)) ∧
        ContDiffOn ℝ ∞ (fun q : Euclidean n × Euclidean 3 ↦
          gradient (fun y ↦ Θ y q.2) q.1)
          (ball 0 d.reference.radius ×ˢ parameterInterior (2 * P.radius)) ∧
        (∀ x ∈ ball 0 d.reference.radius, ∀ z ∈ parameterCube (2 * P.radius),
          determinant (Q x) (gradient (fun y ↦ Θ y z) x) = 0) ∧
        (∀ u, d.reference.sectionEmbedding u ∈ ball 0 d.reference.radius →
          ∀ z ∈ parameterCube (2 * P.radius),
            Θ (d.reference.sectionEmbedding u) z = ⟪u, d.reference.spatialPatch z⟫_ℝ) := by
  obtain ⟨δ, hδ, hcharts⟩ := d.exists_current_chart_of_frame_closeness zero_lt_one
  refine ⟨δ, hδ, ?_⟩
  intro U hU hdomain Q hQ hsmall
  obtain ⟨Φ, χ, hc, ht, hsource, _⟩ := hcharts U hU hdomain Q hQ hsmall
  refine ⟨Φ, χ, carrierPhase χ d.reference.spatialPatch, ht, rfl, ?_⟩
  exact d.current_carrier_identities hP hU Q hQ χ ht hc.section_eq
    hc.momentum_smooth (hc.target_eq.symm ▸ hc.coordinates_smooth) hsource

end JanetCartan.ActualCarriers
