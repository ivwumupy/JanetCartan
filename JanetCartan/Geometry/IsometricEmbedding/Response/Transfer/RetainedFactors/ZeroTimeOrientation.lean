module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.ZeroTimeHessian
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.JointPhaseJets
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.PhaseExtension

/-!
# The retained zero-time Hessian in both literal orientations

The same flow's initial condition identifies the conic zero-time phase on its
original target. Thus forward and literal-adjoint carrier phases have the same
germ at zero elapsed time, without exchanging a weighted inverse for an adjoint.
Consumer: uniform retained Hessian stability in
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace
namespace JanetCartan.ResponseTransfer.RetainedFactors
open CompatibleResponse ArbitraryAccuracy RegularSector.Characteristic ConicPhase EvolutionIntegral
open DirectEvolution EvolutionIntegral.KernelIdentification
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "W" => CarrierVariables (d + 1)
local notation "T" => TwoTimePoint (Euclidean d)

/-- The actual conic phase has the exact zero-time physical pairing on its
original normalized target, by the SAME retained flow's initial condition.
Source: `app:ch_response:eq:response-exact-phase`. -/
theorem retained_conic_elapsedPhase_zero
    (ℓ : Euclidean d →L[ℝ] ℝ)
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph T T}
    (hC : (C : T → T) = twoTimeProjection Φ)
    {z : RootState (Euclidean d)} {a : ℝ}
    (hsource : C.source = ball (z.1, z) a)
    (hi : ∀ v ∈ ball z a, Φ (v, 0) = v)
    {x θ : E} (hx : elapsedChartPoint 0 x θ ∈ domain ℓ C.target) :
    elapsedPhase (curriedPhase ℓ C) 0 x θ = inner ℝ x θ := by
  have hx' : 0 < ℓ (spatialPart θ) ∧
      (x 0, (x 0, (spatialPart x, (ℓ (spatialPart θ))⁻¹ • spatialPart θ))) ∈ C.target := by
    simpa only [domain, mem_ofPred_eq, ConicPhase.normalize, elapsedChartPoint, sub_zero] using hx
  have hd : phase ℓ C (x 0, (x 0, (spatialPart x, spatialPart θ))) =
      inner ℝ (spatialPart x) (spatialPart θ) := by
    apply phase_diagonal ℓ C hx'.1.ne'
    apply ResidualCoordinates.twoTimePhase_diagonal_on_image_box Φ C hC
      (ball z.1 a) (ball z.2 a)
      (fun v hv ↦ hi v (by simpa only [ball_prod_same] using hv))
    refine ⟨?_, ?_⟩
    · exact hx'.2
    · have htarget : (x 0, (x 0, (spatialPart x,
          (ℓ (spatialPart θ))⁻¹ • spatialPart θ))) ∈ C.target := by
        exact hx'.2
      have hs := C.map_target htarget
      rw [hsource] at hs
      simpa only [ball_prod_same, mem_preimage] using hs
  simp only [elapsedPhase, curriedPhase, sub_zero, hd, inner_eq_time_add_spatial]

/-- At time zero both literal orientations have the SAME carrier germ wherever
both original normalized graph points lie in the retained target. No global
phase extension or additional chart is chosen. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem retained_conic_zeroTime_orientations_eventuallyEq
    (adj : Bool) (ℓ : Euclidean d →L[ℝ] ℝ)
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph T T}
    (hC : (C : T → T) = twoTimeProjection Φ)
    {z : RootState (Euclidean d)} {a : ℝ}
    (hsource : C.source = ball (z.1, z) a)
    (hi : ∀ v ∈ ball z a, Φ (v, 0) = v)
    (φ : E → Euclidean 3 → ℝ) (q : E × Euclidean 3) {w : W}
    (hout : carrierGraphPoint false ((0, q), w) ∈ domain ℓ C.target)
    (hsrc : carrierGraphPoint true ((0, q), w) ∈ domain ℓ C.target) :
    (fun v ↦ jointRetainedCarrierPhase adj (curriedPhase ℓ C) φ ((0, q), v)) =ᶠ[𝓝 w]
      elapsedCarrierPhase (curriedPhase ℓ C) 0 φ q := by
  have hpath : Continuous (fun v : W ↦ (((0 : ℝ), q), v)) :=
    continuous_const.prodMk continuous_id
  have ho := ((contDiff_carrierGraphPoint false).continuous.comp hpath).continuousAt.preimage_mem_nhds
    ((isOpen_domain ℓ C.open_target).mem_nhds hout)
  have hs := ((contDiff_carrierGraphPoint true).continuous.comp hpath).continuousAt.preimage_mem_nhds
    ((isOpen_domain ℓ C.open_target).mem_nhds hsrc)
  filter_upwards [ho, hs] with v hvout hvsrc
  have heo := retained_conic_elapsedPhase_zero ℓ hC hsource hi (x := q.1) (θ := v.snd) hvout
  have hes := retained_conic_elapsedPhase_zero ℓ hC hsource hi (x := v.fst) (θ := v.snd) hvsrc
  cases adj
  · rfl
  · simp only [jointRetainedCarrierPhase, ↓reduceIte, CompactTransfer.adjointCarrierPhase,
      elapsedCarrierPhase, carrierPhase, heo, hes]

/-- The entire zero-time averaged Hessian is identical in the two literal
orientations, on the SAME supported segments. This transfers the actual
history inverse bound, not an assumed adjoint estimate. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem retained_conic_zeroTime_averagedHessian_orientation_eq
    (adj : Bool) (ℓ : Euclidean d →L[ℝ] ℝ)
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph T T}
    (hC : (C : T → T) = twoTimeProjection Φ)
    {z : RootState (Euclidean d)} {a : ℝ}
    (hsource : C.source = ball (z.1, z) a)
    (hi : ∀ v ∈ ball z a, Φ (v, 0) = v)
    (φ : E → Euclidean 3 → ℝ) (q : E × Euclidean 3) (v w : W)
    (hout : ∀ s ∈ Icc (0 : ℝ) 1,
      carrierGraphPoint false ((0, q), v + s • (w - v)) ∈ domain ℓ C.target)
    (hsrc : ∀ s ∈ Icc (0 : ℝ) 1,
      carrierGraphPoint true ((0, q), v + s • (w - v)) ∈ domain ℓ C.target) :
    averagedPhaseHessian (fun p u ↦ jointRetainedCarrierPhase adj (curriedPhase ℓ C) φ
      ((0, p), u)) (fun _ ↦ v) q w =
      averagedPhaseHessian (elapsedCarrierPhase (curriedPhase ℓ C) 0 φ) (fun _ ↦ v) q w := by
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa using hs
  exact (retained_conic_zeroTime_orientations_eventuallyEq adj ℓ hC hsource hi φ q
    (hout s hs') (hsrc s hs')).gradient.fderiv_eq

end JanetCartan.ResponseTransfer.RetainedFactors
