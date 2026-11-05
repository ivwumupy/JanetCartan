module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.SupportedData

/-!
# Fixed supported charts inside the actual null-flow tube

The flow producer supplies a fixed cylinder contained in every current tube.
Shrinking the canonical physical/carrier masks before the immersion varies
puts their complete support in that cylinder. This supplies `hsupport` of
`canonical_scalarTransportData_kernel_eq_of_flow`; no varying domain
containment is postulated (`app:ch_background:prop:bg-adjoint`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff

namespace JanetCartan.ContinuumAdjoint.Canonical
open ContinuumRow PhaseExtension ActualCarriers FrozenMenu CurrentFullPhase
open FullPhaseCharts ActualComparison NullTransport ActualFlow FlowAmplitude

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- A positive mask-radius cap places the complete supported physical/carrier
chart in the fixed smaller null-flow cylinder. Both radii are outputs chosen
before the immersion by `exists_projected_local_positive_amplitude`.
The same cap works for every smaller positive mask radius
(`app:ch_background:prop:bg-adjoint`, `app:ch_waves:thm:leading`). -/
theorem exists_supportedChart_flowCylinder_cap (z₀ : Euclidean 3)
    {τ R : ℝ} (hτ : 0 < τ) (hR : 0 < R) :
    ∃ cap > (0 : ℝ), ∀ {a : ℝ}, 0 < a → a < cap →
      MapsTo (fun p : Euclidean n × CarrierParameter ↦
        coordinates (adaptedCoordinates T.data.adapted) (p.1, CanonicalCarrier.parameter p.2))
        (supportedChart z₀ a)
        (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z₀) (R / 32)) := by
  let f : Euclidean n × CarrierParameter → ℝ × (Euclidean (n - 1) × Euclidean 3) :=
    fun p ↦ coordinates (adaptedCoordinates T.data.adapted) (p.1, CanonicalCarrier.parameter p.2)
  let p₀ : Euclidean n × CarrierParameter := (0, z₀ 0, spectatorCenter z₀)
  let V := Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z₀) (R / 32)
  have hf : Continuous f := (coordinates (adaptedCoordinates T.data.adapted)).continuous.comp
    (continuous_fst.prodMk (CanonicalCarrier.parameter.continuous.comp continuous_snd))
  have hV : IsOpen V := isOpen_Ioo.prod isOpen_ball
  have hp : p₀ ∈ f ⁻¹' V := by
    have he : f p₀ = (0, (0, z₀)) := by
      change coordinates (adaptedCoordinates T.data.adapted)
        (0, carrierParameters (spectatorCenter z₀, z₀ 0)) = (0, (0, z₀))
      rw [ActualComparison.carrierParameters_spectatorCenter]
      simp
    change f p₀ ∈ V
    rw [he]
    exact ⟨⟨by linarith, hτ⟩, mem_ball_self (by positivity)⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp ((hV.preimage hf).mem_nhds hp)
  refine ⟨δ / 8, by positivity, ?_⟩
  intro a ha hacap p hp
  apply hball
  rw [mem_ball, Prod.dist_eq, max_lt_iff]
  refine ⟨(mem_closedBall.mp hp.1).trans_lt (by linarith), ?_⟩
  rw [Prod.dist_eq, max_lt_iff]
  exact ⟨(mem_closedBall.mp hp.2.1).trans_lt (by linarith),
    (mem_closedBall.mp hp.2.2).trans_lt (by linarith)⟩

/-- The actual producer's fixed-cylinder inclusion discharges containment in
every retained flow tube. The cap is chosen before that tube and the immersion
(`app:ch_background:prop:bg-adjoint`). -/
theorem exists_supportedChart_flowTube_cap (z₀ : Euclidean 3)
    {τ R : ℝ} (hτ : 0 < τ) (hR : 0 < R) :
    ∃ cap > (0 : ℝ), ∀ {a : ℝ}, 0 < a → a < cap →
      ∀ D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
        Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z₀) (R / 32) ⊆ D →
        MapsTo (fun p : Euclidean n × CarrierParameter ↦
          coordinates (adaptedCoordinates T.data.adapted) (p.1, CanonicalCarrier.parameter p.2))
          (supportedChart z₀ a) D := by
  obtain ⟨cap, hcap, hmaps⟩ := exists_supportedChart_flowCylinder_cap T z₀ hτ hR
  exact ⟨cap, hcap, fun ha hacap _ hD ↦ fun _ hp ↦ hD (hmaps ha hacap hp)⟩

end JanetCartan.ContinuumAdjoint.Canonical
