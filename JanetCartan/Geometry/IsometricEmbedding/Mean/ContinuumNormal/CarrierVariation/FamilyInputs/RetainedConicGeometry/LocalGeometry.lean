module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedConicGeometry.NormBuffers
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedConicGeometry.InverseStability
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedConicGeometry.JacobianGap

/-!
# Common local geometry inside the original retained field chart

This assembles the refinement, forward comparison and buffered inverse
construction on the same supplied reference transport. The input field chart
is supplied by `exists_retained_field_norm_buffers`; the central reference
half-gap comes from the source conic chart and its transport identification.
The primitive order-two threshold is subsequently discharged by the retained
Hamilton/immersion comparison. Extension to the original uncut conic support
is a further obligation, not asserted by this local theorem.

Consumers: `exists_retained_conic_primitives_sub_tolerance`,
`exists_retained_conic_densityPair_comparison`, and
`exists_retained_originalScalar_coefficient_controls`.
Sources: `app:ch_background:eq:bg-Psi`, `app:ch_background:eq:bg-jacobian`,
and `app:ch_osc:prop:osc-normal`, Step 4'.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ContinuumNormalReduction.TransportSymbol ContinuumRow WideDensity

/-- Construct all local norm and inverse domains from the retained reference
at its original center. The full augmented normalization is refined before
the perturbation threshold and masks are chosen. Literal Jacobian positivity
and smoothness are conclusions. This closes the local geometric portion of
`bg-Psi`; radial extension and the retained immersion instantiation remain
separate steps of the same construction. -/
theorem exists_retained_local_geometry {n : ℕ}
    (D : PrimitiveNormChart (Euclidean n × CarrierParameter))
    {z : CarrierParameter} (hcenter : D.center = (0, z))
    {η : Euclidean (n - 1)} (hη : η ≠ 0)
    {H : Set (InputVariables n)} (hH : IsOpen H)
    (hpH : (((0, 0), z, η) : InputVariables n) ∈ H)
    {Y₀ : Euclidean n × CarrierParameter → Euclidean (n - 1)}
    (hY₀ : ContDiffOn ℝ ∞ Y₀ D.region)
    (A₀ : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    (hgap₀ : ‖A₀.symm.toContinuousLinearMap.comp
      (fderiv ℝ (augmentedTransportGradient Y₀) ((0, 0), z, η)) -
        ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2)
    (slice : TransportSliceCoordinates n) :
    ∃ E : CoefficientNormCharts n, E.field = D ∧
    ∃ Ki W Bi : Set (InputVariables n),
      IsCompact Ki ∧ Convex ℝ Ki ∧ IsOpen W ∧ Ki ⊆ W ∧ IsCompact Bi ∧ W ⊆ Bi ∧ Bi ⊆ H ∧
      (((0, 0), z, η) : InputVariables n) ∈ interior Ki ∧
      (∀ p ∈ W, ‖η‖ / 2 < ‖p.2.2‖) ∧
      (∀ p ∈ Ki, E.Contains p) ∧
      (∀ side, MapsTo (densityEndpoint side) W E.field.carrier) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W E.field.carrier) ∧
      (∀ t ∈ Ioo (-1 : ℝ) 2, MapsTo (transportSegmentInput n t) W E.field.region) ∧
    ∃ A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2,
    ∃ Q Ω : Set (Variables n × Euclidean 2), IsCompact Q ∧ IsOpen Ω ∧ Q ⊆ Ω ∧
      augmentedTransportGradient Y₀ ((0, 0), z, η) ∈ interior Q ∧
    ∃ gap > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ Y : Euclidean n × CarrierParameter → Euclidean (n - 1),
        ContDiffOn ℝ ∞ Y E.field.region → cNorm E.field.carrier 2 (Y - Y₀) < δ →
      ∃ u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1),
        ContDiffOn ℝ ∞ u Ω ∧ MapsTo (inverseCoordinates u) Ω (interior Ki) ∧
        MapsTo (inverseCoordinates u) Q Ki ∧
        (∀ q ∈ Ω, transportAveragedGradient Y (inverseCoordinates u q) = q.1.2.2) ∧
        (∀ p ∈ Ki, ‖A.symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient Y) p) -
            ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
        (∀ p ∈ Bi, gap ≤ transportAbsoluteJacobian slice Y p) ∧
        ContDiffOn ℝ ∞ (transportAbsoluteJacobian slice Y) W ∧
        InjOn (augmentedTransportGradient Y) Ki ∧
        (∀ (v : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)) (q),
          q ∈ Ω → inverseCoordinates v q ∈ Ki →
          transportAveragedGradient Y (inverseCoordinates v q) = q.1.2.2 → u q = v q) := by
  let p₀ : InputVariables n := ((0, 0), z, η)
  obtain ⟨b, hb, hfreq, hend, hseg, hsegT⟩ := exists_retained_segment_buffer D hcenter hη
  have hIIt : Icc (0 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 2 := fun t ht ↦
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hf₀ := augmentedTransportGradient_contDiffOn isOpen_ball D.isOpen_region
    isOpen_Ioo hIIt hsegT hY₀
  obtain ⟨A, _, ρ, hρ, hρH, gap, hgap, hquarter, hJac, _⟩ :=
    exists_retained_augmented_refinement (isOpen_ball.inter hH) ⟨mem_ball_self hb, hpH⟩
      (hf₀.mono inter_subset_left) A₀ hgap₀ slice
  let Ki := closedBall p₀ ρ
  let Bi := closedBall p₀ (2 * ρ)
  let W := interior Bi
  have hρBall : Bi ⊆ ball p₀ b := fun p hp ↦ (hρH hp).1
  have hBiH : Bi ⊆ H := fun p hp ↦ (hρH hp).2
  have hKiBi : Ki ⊆ Bi := closedBall_subset_closedBall (by linarith)
  have hKiH : Ki ⊆ ball p₀ b := hKiBi.trans hρBall
  have hWBi : W ⊆ Bi := interior_subset
  have hWH : W ⊆ ball p₀ b := hWBi.trans hρBall
  have hKiW : Ki ⊆ W :=
    (closedBall_subset_ball (by linarith : ρ < 2 * ρ)).trans ball_subset_interior_closedBall
  have hpKi : p₀ ∈ interior Ki := mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds _ hρ)
  obtain ⟨E, hED, _, _, _, hcontains, _⟩ := exists_coefficientNormCharts_on_compact D
    (isCompact_closedBall p₀ ρ) (fun p hp ↦ ⟨hend false (hKiH hp), hend true (hKiH hp)⟩)
  obtain ⟨Q, Ω, hQ, hΩ, hQΩ, hcenterQ, δI, hδI, hinv⟩ :=
    exists_retained_transport_inverse_stability
      (isCompact_closedBall p₀ ρ) (convex_closedBall _ _) hpKi isOpen_ball hKiH
      (isCompact_closedBall p₀ b) ball_subset_closedBall
      D.isOpen_region (isCompact_closedBall D.center D.radius) D.ball_subset
      isOpen_Ioo hIIt hsegT hseg hY₀ A (fun p hp ↦ hquarter p (hKiBi hp))
  obtain ⟨δJ, hδJ, hjac⟩ := exists_retained_literal_jacobian_gap
    (isCompact_closedBall p₀ (2 * ρ)) isOpen_ball hρBall
    (isCompact_closedBall p₀ b) ball_subset_closedBall
    D.isOpen_region (isCompact_closedBall D.center D.radius) D.ball_subset
    isOpen_Ioo hIIt hsegT hseg hY₀ A slice hgap hJac
  refine ⟨E, hED, Ki, W, Bi, isCompact_closedBall _ _, convex_closedBall _ _,
    isOpen_interior, hKiW, isCompact_closedBall _ _, hWBi, hBiH, hpKi,
    fun p hp ↦ hfreq p (hWH hp), hcontains, ?_, ?_, ?_,
    A, Q, Ω, hQ, hΩ, hQΩ, hcenterQ, gap / 2, half_pos hgap,
    min δI δJ, lt_min hδI hδJ, ?_⟩
  · intro side p hp
    rw [hED]
    exact hend side (hWH hp)
  · intro t ht p hp
    rw [hED]
    exact hseg t ht (hWH hp)
  · intro t ht p hp
    rw [hED]
    exact hsegT t ht (hWH hp)
  · intro Y hY hnear
    rw [hED] at hY hnear
    obtain ⟨u, hu, hrange, hrangeQ, heq, hdiff, hinj, huniq⟩ :=
      hinv Y hY (hnear.trans_le (min_le_left _ _))
    obtain ⟨hJ, hJs⟩ := hjac Y hY (hnear.trans_le (min_le_right _ _))
    exact ⟨u, hu, hrange, hrangeQ, heq, hdiff, hJ, hJs, hinj, huniq⟩

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
