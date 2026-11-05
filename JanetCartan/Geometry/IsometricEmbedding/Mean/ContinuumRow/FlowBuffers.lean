module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalCarrier
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualComparison.Boxes
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.Buffers
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.PrimitiveNorms

/-!
# Fixed coefficient neighborhoods inside the actual flow tube

The retained positive transport construction supplies positive `R` and `τ`.
This leaf constructs a common coefficient neighborhood inside its smaller
working tube, the Hamilton domain and the detector ball. It supplies the
fixed domain hypotheses of `exists_actual_canonical_primitive_controls`;
no coefficient norm or current-flow estimate is assumed.

Source: `app:ch_background:eq:bg-mixed-input` and `bg-T`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 200000
open Set Metric
open scoped ContDiff
namespace JanetCartan.ContinuumRow.CanonicalCarrier
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open NullTransport ActualFlow FlowAmplitude ActualComparison
open ContinuumNormalReduction.TransportSymbol

/-- A fixed product neighborhood fits inside the actual flow's compact working
tube, the phase domain and a detector ball. It is chosen before the current
immersion and before any norm budget (`bg-mixed-input`, `bg-T`). -/
theorem exists_canonical_flow_buffers {n : ℕ} {P : Patch n} {c C : ℝ}
    (hP : P.IsValid c C) {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {K : Set (Euclidean n)}
    (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (z : Euclidean 3) (hz : z ∈ parameterCube P.radius)
    {R τ : ℝ} (hR : 0 < R) (hτ : 0 < τ) :
    ∃ ε > (0 : ℝ), ∃ ρdet > (0 : ℝ),
      let X := ball (0 : Euclidean n) ε
      let V := ball (z 0, spectatorCenter z) ε
      let ψ := fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)
      let C := coordinates (adaptedCoordinates T.data.adapted)
      X ⊆ K ∧ X ⊆ U ∧
      MapsTo ψ (X ×ˢ V) (ball (0 : Euclidean n) T.physicalRadius ×ˢ
        parameterInterior (2 * P.radius)) ∧
      MapsTo ψ (X ×ˢ V) (C.symm ''
        (Icc (-τ / 2) (τ / 2) ×ˢ closedBall ((0 : Euclidean (n - 1)), z) (R / 64))) ∧
      MapsTo (fun p ↦ C (ψ p)) (X ×ˢ V)
        (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 32)) ∧
      X ×ˢ V ⊆ ball (0 : Euclidean n) T.family.radius ×ˢ
        (parameter ⁻¹' parameterInterior (3 * P.radius / 2)) ∧
      MapsTo Prod.fst (closedBall ((0 : Euclidean n), z) ρdet)
        (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) ∧
      closedBall ((0 : Euclidean n), z) ρdet ⊆
        ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius) ∧
      MapsTo ψ (X ×ˢ V) (closedBall ((0 : Euclidean n), z) ρdet) := by
  let ψ := fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)
  let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  let zc : CarrierParameter := (z 0, spectatorCenter z)
  have hψ : Continuous ψ := continuous_fst.prodMk (parameter.continuous.comp continuous_snd)
  have hψ₀ : ψ (0, zc) = (0, z) := by
    simp only [ψ, zc, parameter_apply, carrierParameters_spectatorCenter]
  have hC₀ : C (ψ (0, zc)) = (0, (0, z)) := by
    rw [hψ₀]
    simp [C, coordinates_apply]
  have hz2 : z ∈ parameterInterior (2 * P.radius) := fun i ↦
    (hz i).trans_lt (by linarith [hP.1])
  have hz3 : z ∈ parameterInterior (3 * P.radius / 2) := fun i ↦
    (hz i).trans_lt (by linarith [hP.1])
  obtain ⟨ρdet, _, hρdet, _, hdet, hxdet, _⟩ := exists_adapted_coefficient_ball T
    (isOpen_ball.prod (isOpen_parameterInterior (2 * P.radius))) z
    ⟨mem_ball_self T.physicalRadius_pos, hz2⟩
  let W : Set (Euclidean n × CarrierParameter) :=
    ψ ⁻¹' ball ((0 : Euclidean n), z) ρdet ∩
    (fun p ↦ C (ψ p)) ⁻¹'
      (Ioo (-τ / 2) (τ / 2) ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 64)) ∩
    (ball (0 : Euclidean n) T.family.radius ×ˢ
      (parameter ⁻¹' parameterInterior (3 * P.radius / 2)))
  have hW : IsOpen W :=
    ((isOpen_ball.preimage hψ).inter
      ((isOpen_Ioo.prod isOpen_ball).preimage (C.continuous.comp hψ))).inter
      (isOpen_ball.prod ((isOpen_parameterInterior _).preimage parameter.continuous))
  have hW₀ : ((0 : Euclidean n), zc) ∈ W := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change ψ (0, zc) ∈ ball ((0 : Euclidean n), z) ρdet
      rw [hψ₀]
      exact mem_ball_self hρdet
    · change C (ψ (0, zc)) ∈ Ioo (-τ / 2) (τ / 2) ×ˢ
        ball ((0 : Euclidean (n - 1)), z) (R / 64)
      rw [hC₀]
      exact ⟨⟨by linarith, by linarith⟩, mem_ball_self (by positivity)⟩
    · exact ⟨mem_ball_self T.family.radius_pos,
        by simpa only [mem_preimage, zc, parameter_apply, carrierParameters_spectatorCenter] using hz3⟩
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hW₀)
  have hsub : ball (0 : Euclidean n) ε ×ˢ ball zc ε ⊆ W := by
    rw [ball_prod_same]
    exact hεW
  have hmaps : MapsTo ψ (ball (0 : Euclidean n) ε ×ˢ ball zc ε)
      (closedBall ((0 : Euclidean n), z) ρdet) := fun _ hp ↦
    ball_subset_closedBall (hsub hp).1.1
  have hXK : ball (0 : Euclidean n) ε ⊆ K := by
    intro x hx
    have hzmem : zc ∈ ball zc ε := mem_ball_self hε
    have hpair : (x, zc) ∈ ball (0 : Euclidean n) ε ×ˢ ball zc ε := ⟨hx, hzmem⟩
    have hp : ψ (x, zc) ∈ closedBall ((0 : Euclidean n), z) ρdet := hmaps hpair
    have hxball : x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius :=
      hxdet (x := ψ (x, zc)) hp
    exact hball hxball
  refine ⟨ε, hε, ρdet, hρdet, hXK, hXK.trans hKU,
    fun _ hp ↦ hdet (hmaps hp), ?_, ?_, fun _ hp ↦ (hsub hp).2,
    hxdet, hdet, hmaps⟩
  · intro p hp
    refine ⟨C (ψ p), ?_, C.symm_apply_apply _⟩
    have h := (hsub hp).1.2
    exact ⟨⟨h.1.1.le, h.1.2.le⟩, ball_subset_closedBall h.2⟩
  · intro p hp
    have h := (hsub hp).1.2
    exact ⟨⟨by linarith [h.1.1], by linarith [h.1.2]⟩,
      ball_subset_ball (by linarith : R / 64 ≤ R / 32) h.2⟩

/-- A field chart contained in a product coefficient neighborhood has its two
closed-ball projections there. This supplies the exact projection premises of
`exists_canonical_primitive_controls` without a second chart (`bg-mixed-input`). -/
theorem coefficientNormCharts_ball_projections {n : ℕ} (D : CoefficientNormCharts n)
    {X : Set (Euclidean n)} {V : Set CarrierParameter}
    (hregion : D.field.region ⊆ X ×ˢ V) :
    closedBall D.field.center.1 D.field.radius ⊆ X ∧
      closedBall D.field.center.2 D.field.radius ⊆ V := by
  have hsub : closedBall D.field.center.1 D.field.radius ×ˢ
      closedBall D.field.center.2 D.field.radius ⊆ X ×ˢ V := by
    rw [closedBall_prod_same]
    exact D.field.ball_subset.trans hregion
  constructor
  · intro x hx
    have hc : D.field.center.2 ∈ closedBall D.field.center.2 D.field.radius :=
      mem_closedBall_self D.field.radius_pos.le
    exact (hsub (a := (x, D.field.center.2)) ⟨hx, hc⟩).1
  · intro z hz
    have hc : D.field.center.1 ∈ closedBall D.field.center.1 D.field.radius :=
      mem_closedBall_self D.field.radius_pos.le
    exact (hsub (a := (D.field.center.1, z)) ⟨hc, hz⟩).2

end JanetCartan.ContinuumRow.CanonicalCarrier
