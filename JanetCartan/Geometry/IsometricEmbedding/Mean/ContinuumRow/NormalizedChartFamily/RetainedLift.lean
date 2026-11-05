module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedChartFamily.LiftConstruction
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.Chart

/-!
# Retaining a literal lift without changing the original chart domain

At chart selection, use the literal forward/backward maps of an actual smooth
lift. ODE uniqueness proves equality with the supplied chart on its prescribed
domains, and the image descriptions identify the domains themselves. The
inverse's extension outside that domain is explicitly constructed, not inferred
from the old inverse laws.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedChartFamily
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference
open FlowConstruction

/-- Enrich a chart at its original selection with a literal autonomous lift,
preserving its exact frame, flow tube, forward flow on the initial cylinder,
inverse on the flow tube, and every prescribed scalar there. The constructed
inverse has the backward-flow formula on the full cylinder, including points
outside the tube. No equality with the old arbitrary extension is claimed on
those points. This applies directly to the raw charts supplied by the common
initializer, without requiring it to expose another coefficient interface.
Consumers: the normalized inverse profiles and the same-domain carrier/scalar
assembly (`app:ch_waves:thm:leading`, `app:ch_background:eq:bg-T`,
`app:ch_background:prop:bg-normalized`). -/
theorem exists_retained_chart_lift_enrichment
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    {T : PatchQuantitativeFamily P U hU}
    {Ω K : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {p₀ : Euclidean (n - 1) × Euclidean 3} {R B τ : ℝ} {row col : Fin n}
    {F : Euclidean n → Euclidean N}
    (hR : 0 < R) (hB : 0 ≤ B)
    (hτ : τ = existenceTime R (liftedLowBound T B) / 4)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, p₀) R) K)
    (original : Chart T Ω K p₀ R B τ row col F) :
    ∃ current : Chart T Ω K p₀ R B τ row col F,
      ∃ Ψ : (ℝ × (Euclidean (n - 1) × Euclidean 3)) × ℝ →
          ℝ × (Euclidean (n - 1) × Euclidean 3),
        current.Q = original.Q ∧ current.D = original.D ∧
        ODE.IsSmoothFlowOn (liftedDirection T current.Q row col) (0, p₀) R (R / 2)
          (existenceTime R (liftedLowBound T B)) Ψ ∧
        current.forward = forwardFromLift Ψ ∧ current.inverse = footpointFromLift Ψ ∧
        EqOn current.forward original.forward (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) ∧
        EqOn current.inverse original.inverse original.D ∧
        ∀ initial : Euclidean (n - 1) × Euclidean 3 → ℝ,
          EqOn (current.scalar initial) (original.scalar initial)
            ((coordinates (adaptedCoordinates T.data.adapted)) ⁻¹' original.D) := by
  subst τ
  let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  let M := liftedLowBound T B
  let ε := existenceTime R M
  let τ := ε / 4
  have hM : 0 ≤ M := liftedLowBound_nonneg T hB
  have hε : 0 < ε := existenceTime_pos hR hM
  have hτ : 0 < τ := div_pos hε (by norm_num)
  have hτR : τ ≤ R / 16 := by
    have hh := (existenceTime_le hR hM).1
    dsimp [τ, ε]
    linarith
  have hb (q) (hq : q ∈ closedBall ((0 : ℝ), p₀) R) :=
    liftedDirection_low_bounds T original.Q row col hΩ original.direction_smooth
      hK hKΩ hB original.direction_bound (hbuffer hq)
  have hV := contDiffOn_liftedDirection T original.Q row col original.direction_smooth
  have hW : IsOpen (C.symm ⁻¹' Ω) := hΩ.preimage C.symm.continuous
  obtain ⟨Ψ, hΨ, D, hD, hsmall, hbig, himage, hcoeff, hφ, hy, hφD, hyD,
    hi, hyφ, hφy, hφz, hyz, hode, hφwide, hywide⟩ :=
    exists_buffered_chart_with_lift hW (fun q hq ↦ hKΩ (hbuffer hq)) hV hR hM hb
      (fun _ ↦ rfl) (fun _ ↦ rfl)
  have hlip : LipschitzOnWith ⟨M, hM⟩ (liftedDirection T original.Q row col)
      (closedBall (0, p₀) R) :=
    (convex_closedBall _ _).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun q hq ↦ (hV.contDiffAt (hW.mem_nhds (hKΩ (hbuffer hq)))).differentiableAt (by simp))
      (fun q hq ↦ by exact_mod_cast (hb q hq).2)
  have hrange : MapsTo (fun q ↦ (q.1, original.forward q))
      (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) (closedBall (0, p₀) R) := by
    intro q hq
    have hh := original.subset_big (original.forward_range hq)
    rw [mem_closedBall, Prod.dist_eq, max_le_iff]
    refine ⟨?_, (mem_ball.mp hh.2).le.trans (by linarith)⟩
    simpa only [Real.dist_eq, sub_zero] using
      (abs_lt.mpr hh.1).le.trans (by linarith : τ ≤ R)
  have hforward := NullFlowDependence.forward_eq_of_lift hR hτ
    (show τ ≤ ε by dsimp [τ]; linarith) (fun _ ↦ rfl) hlip hΨ original.initial original.ode hrange
  have hinverse := NullFlowDependence.footpoint_eq_of_lift hR hτ
    (show τ < ε / 2 by dsimp [τ]; linarith) hτR (fun _ ↦ rfl) hlip hΨ
    original.initial original.ode hrange original.subset_big original.inverse_range original.forward_inverse
  have hDeq : D = original.D := by
    rw [himage, original.domain_eq]
    apply Set.image_congr
    intro q hq
    exact Prod.ext rfl (hforward hq).symm
  let current : Chart T Ω K p₀ R B τ row col F := {original with
    D := D
    forward := forwardFromLift Ψ
    inverse := footpointFromLift Ψ
    domain_eq := himage
    domain_open := hD
    small_subset := hsmall
    subset_big := hbig
    domain_coefficients := hcoeff
    forward_smooth := hφ
    inverse_smooth := hy
    forward_range := hφD
    inverse_range := hyD
    initial := hi
    inverse_forward := hyφ
    forward_inverse := hφy
    forward_parameter := hφz
    inverse_parameter := hyz
    ode := hode
    forward_buffer_smooth := hφwide
    inverse_buffer_smooth := hywide}
  refine ⟨current, Ψ, rfl, hDeq, hΨ, rfl, rfl, hforward.symm, hinverse.symm, ?_⟩
  intro initial w hw
  have hinv : current.inverse (C w) = original.inverse (C w) := (hinverse hw).symm
  have hp := original.inverse_range hw
  have h0 : (0 : ℝ) ∈ Ioo (-τ) τ := ⟨neg_neg_of_pos hτ, hτ⟩
  have hsegment : uIcc (0 : ℝ) (C w).1 ⊆ Ioo (-τ) τ :=
    ordConnected_Ioo.uIcc_subset h0 hp.1
  have hscalar : ∫ s in (0 : ℝ)..(C w).1,
      carrierTransportPotential T original.Q F row col
        (C.symm (s, current.forward (s, original.inverse (C w)))) =
      ∫ s in (0 : ℝ)..(C w).1,
        carrierTransportPotential T original.Q F row col
          (C.symm (s, original.forward (s, original.inverse (C w)))) := by
    apply intervalIntegral.integral_congr
    intro s hs
    exact congrArg (fun v ↦ carrierTransportPotential T original.Q F row col (C.symm (s, v)))
      (hforward (x := (s, original.inverse (C w))) ⟨hsegment hs, hp.2⟩).symm
  simp only [Chart.scalar, carrierScalarAmplitude, transportFromFootpoint,
    characteristicTransport, scalarTransport, transportFactor, flowTransportCoefficient]
  change _ * initial (current.inverse (C w)) = _ * initial (original.inverse (C w))
  rw [hinv]
  exact congrArg (fun z : ℝ ↦ Real.exp (-z) * initial (original.inverse (C w))) hscalar

end JanetCartan.ContinuumRow.NormalizedChartFamily
