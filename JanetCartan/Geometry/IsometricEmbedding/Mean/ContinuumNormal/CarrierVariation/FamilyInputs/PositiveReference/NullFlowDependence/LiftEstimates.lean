module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence.Identification
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualFlow.HighBounds
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedCarrierJets.FixedPullback

/-!
# Finite-order differences of null-characteristic lifts

Fixed linear pullbacks transfer the primitive direction difference to the
autonomous lift without derivative loss. The joint ODE comparison then controls
both forward and backwards characteristic restrictions. All thresholds precede
the varying coefficient and its solution.

Consumer: the retained-map comparison in `NullFlowDependence`, and hence
`app:ch_background:prop:bg-frame` and `app:ch_osc:prop:osc-normal`, Step 4'.
The actual low bounds and buffers are produced by `ActualAmplitude.UniformFlow`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence
open NullTransport.ActualFlow

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Apply the fixed characteristic restriction estimate to a difference of
lifts (`app:ch_waves:thm:leading`). No derivative is lost in either restriction. -/
theorem cNorm_characteristics_sub_le_flow
    {Ψ Ψ₀ : (ℝ × E) × ℝ → ℝ × E} {p₀ : E} {R T τ : ℝ}
    (hR : 0 < R) (hT : 0 < T) (hτ : 0 ≤ τ) (hτT : τ < T) (hτR : τ ≤ R / 4)
    (hΨ : ContDiffOn ℝ ∞ Ψ (ball (0, p₀) (R / 2) ×ˢ Ioo (-T) T))
    (hΨ₀ : ContDiffOn ℝ ∞ Ψ₀ (ball (0, p₀) (R / 2) ×ˢ Ioo (-T) T)) (m : ℕ) :
    cNorm (Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)) m
        (forwardFromLift Ψ - forwardFromLift Ψ₀) +
      cNorm (Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)) m
        (footpointFromLift Ψ - footpointFromLift Ψ₀) ≤
      (2 * (m + 1 : ℝ)) *
        cNorm (closedBall (0, p₀) (R / 4) ×ˢ Icc (-τ) τ) m (Ψ - Ψ₀) := by
  exact cNorm_characteristics_le_flow hR hT hτ hτT hτR (hΨ.sub hΨ₀) m

/-- At a fixed reference, primitive lifted-field differences control both
actual characteristic restrictions in every finite order. This is the joint
flow stability input to the retained-map and scalar comparisons
(`app:ch_background:prop:bg-frame`). -/
theorem exists_cNorm_lift_characteristics_sub_lt
    {Ω : Set (ℝ × E)} {p₀ : E} {R T τ : ℝ}
    {V₀ : ℝ × E → ℝ × E} {Ψ₀ : (ℝ × E) × ℝ → ℝ × E}
    (hΩ : IsOpen Ω) (hbuffer : closedBall (0, p₀) R ⊆ Ω) (hR : 0 < R)
    (hV₀ : ContDiffOn ℝ ∞ V₀ Ω)
    (hΨ₀ : ODE.IsSmoothFlowOn V₀ (0, p₀) R (R / 2) T Ψ₀)
    (hτ : 0 < τ) (hτT : τ < T) (hτR : τ ≤ R / 4)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (V : ℝ × E → ℝ × E) (Ψ : (ℝ × E) × ℝ → ℝ × E),
      ContDiffOn ℝ ∞ V Ω → ODE.IsSmoothFlowOn V (0, p₀) R (R / 2) T Ψ →
      cNorm (closedBall (0, p₀) R) m (V - V₀) < δ →
      cNorm (Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)) m
          (forwardFromLift Ψ - forwardFromLift Ψ₀) +
        cNorm (Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)) m
          (footpointFromLift Ψ - footpointFromLift Ψ₀) < ε := by
  have hC : 0 < 2 * (m + 1 : ℝ) := by positivity
  obtain ⟨δ, hδ, hb⟩ := ODE.exists_cNorm_flow_sub_lt hΩ hbuffer hV₀ hΨ₀
    (by linarith : 0 < R / 4) (by linarith : R / 4 < R / 2)
    hτ hτT m (div_pos hε hC)
  refine ⟨δ, hδ, fun V Ψ hV hΨ hsmall ↦ ?_⟩
  apply (cNorm_characteristics_sub_le_flow hR (hτ.trans hτT) hτ.le hτT hτR
    hΨ.smooth hΨ₀.smooth m).trans_lt
  exact (mul_lt_mul_of_pos_left (hb V Ψ hV hΨ hsmall) hC).trans_eq
    (mul_div_cancel₀ ε hC.ne')

open ActualCarriers FrozenMenu CurrentFullPhase

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The difference of the literal autonomous lifts is bounded linearly by
the difference of `carrierTransportDirection` on the original coefficient
compact set, at the SAME order. The constant depends only on the fixed
coordinate maps and compact buffers (`app:ch_waves:thm:leading`).
This is the primitive input to positive-reference flow comparison. -/
theorem exists_liftedDirection_sub_bound
    {K : Set (Euclidean n × Euclidean 3)} (hK : IsCompact K)
    (p₀ : Euclidean (n - 1) × Euclidean 3) (R : ℝ)
    (hmaps : MapsTo (NullTransport.FlowAmplitude.coordinates
      (adaptedCoordinates T.data.adapted)).symm (closedBall (0, p₀) R) K) :
    ∃ B : ℕ → ℝ, (∀ m, 0 < B m) ∧
      ∀ (Q Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold}) (row col : Fin n),
        (∀ w ∈ K, ContDiffAt ℝ ∞ (NullTransport.carrierTransportDirection T Q row col) w) →
        (∀ w ∈ K, ContDiffAt ℝ ∞ (NullTransport.carrierTransportDirection T Q₀ row col) w) →
        ∀ m, cNorm (closedBall (0, p₀) R) m
          (liftedDirection T Q row col - liftedDirection T Q₀ row col) ≤
          B m * cNorm K m
            (NullTransport.carrierTransportDirection T Q row col -
              NullTransport.carrierTransportDirection T Q₀ row col) := by
  let C := (NullTransport.FlowAmplitude.coordinates (Z := Euclidean 3)
    (adaptedCoordinates T.data.adapted)).symm
  let A : Euclidean n →L[ℝ] ℝ × (Euclidean (n - 1) × Euclidean 3) :=
    (0 : Euclidean n →L[ℝ] ℝ).prod ((directionProjection T).prod 0)
  obtain ⟨H, hH, hb⟩ := ConstructedCarrierJets.exists_cNorm_fixed_pullback_le
    (G := Euclidean n) (isCompact_closedBall (0, p₀) R) hK
    (fun _ _ ↦ C.contDiff.contDiffAt) hmaps
  refine ⟨fun m ↦ 1 + ‖A‖ * H m, fun m ↦ by have := hH m; positivity, ?_⟩
  intro Q Q₀ row col hd hd₀ m
  let d := NullTransport.carrierTransportDirection T Q row col -
    NullTransport.carrierTransportDirection T Q₀ row col
  have hreg : ∀ w ∈ K, ContDiffAt ℝ ∞ d w := fun w hw ↦ (hd w hw).sub (hd₀ w hw)
  have heq : liftedDirection T Q row col - liftedDirection T Q₀ row col =
      A ∘ (d ∘ C) := by
    funext q
    simp [liftedDirection, A, d, C, directionProjection, map_sub]
  rw [heq]
  have hpost := FullPhaseCharts.InverseEstimates.cNorm_postLinear_le_on
    (isCompact_closedBall (0, p₀) R) m A
    (fun q hq ↦ ((hreg _ (hmaps hq)).comp q C.contDiff.contDiffAt).of_le (by simp))
  apply hpost.trans
  calc
    _ ≤ ‖A‖ * (H m * cNorm K m d) :=
      mul_le_mul_of_nonneg_left (hb d hreg m) (norm_nonneg _)
    _ ≤ (1 + ‖A‖ * H m) * cNorm K m d := by
      nlinarith [cNorm_nonneg K m d]

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence
