module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.UniformCritical.RootDomain
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.UniformCritical.DiagonalBuffers.Domains

/-!
# Actual uniform primary-diagonal buffers

Use the original primary family, coefficient root and normalized section.
The enlarged integration domain contains the full annular frequency carrier
and a fourfold metric ball around every actual primary diagonal. All choices
precede the varying coefficient field. The original `C⁶` comparison proves
gradient containment and the eikonal equation, with one combined threshold.

Consumer: the quantitative stationary branch and both orientations of
`app:ch_response:eq:direct-envelope-profile`. This constructs diagonal
margins, not moving stationary points or a source-interval comparison.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu CompatibleResponse ArbitraryAccuracy
open RegularSector.Characteristic RegularSector.Characteristic.AlgebraicChart
open RegularSector.Characteristic.RootFamily ResponseTransfer.RetainedFactors
open RegularSector.Characteristic.ConicPhase RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
open RegularSector.Characteristic.AmplitudeBounds

variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d + 1)
local notation "Coeff" => Fin (d + 1) → MetricTensor (d + 1)

/-- Construct common output/parameter domains and a fourfold integration
margin for the literal primary diagonal. The physical premises are the FIXED
root-ball projection of the retained producer, the inclusion of its physical
coefficient ball in the original primary domain, and the geometric comparison
`ε ≤ L`. For the original `retainedRadius b ρ`, the last comparison is proved
by `retainedRadius_lt_rootRadius_of_original_chart` from the SAME retained
chart. `retained_primary_physical_buffer` combines the physical inclusions.
Every analytic premise is discharged by
`exists_uniform_primary_pair_neighborhood` and
`exists_uniform_retained_primary_root_domain`.

The original frequency support is the carrier with angular radius `ε / 2`,
as in `AnnularMasks`, including its entire radial interval. The integration
source box has radius `ε`, twice the mask box radius. The root equation holds
on the entire original physical ball and fourfold parameter buffer
(`app:ch_response:eq:response-exact-phase`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_uniform_retained_diagonal_buffers
    {c C₀ : ℝ} (hP : P.IsValid c C₀)
    (hframe : closedBall (0 : E) T.data.localReference.stateRadius ⊆ U)
    {c₀ : Euclidean 3} (hc₀ : c₀ ∈ parameterInterior (2 * P.radius))
    (hξ : P.toFun c₀ ≠ 0) (x₀ : E) (i r c' : Fin (d + 1))
    (ℓ : Euclidean d →L[ℝ] ℝ)
    (H : Coeff × Euclidean d → ℝ) {rootRadius L μ ν : ℝ}
    (hr : 0 < rootRadius) (hL : 0 < L) (hμ : 0 < μ) (hν : 0 < ν)
    (hH : RootBuffer i r c' (cubeStress (d + 1)) (P.toFun c₀) H rootRadius L μ ν)
    {ε aperture gap radius : ℝ} (hε : 0 < ε) (hAp : 0 < aperture) (hg : 0 < gap)
    (hℓ : ℓ (coordinateSplit i (P.toFun c₀)).2 = 1)
    (hApθ : |P.toFun c₀ i| < aperture)
    {RQ : ℝ} (hKprimary : closedBall x₀ RQ ⊆ ball 0 T.physicalRadius)
    (hεL : ε ≤ L)
    (hrootPhysical : MapsTo (rootPhysicalPosition (coordinateSplit i))
      (closedBall
        ((coordinateSplit i x₀).1, ((coordinateSplit i x₀).2,
          (coordinateSplit i (P.toFun c₀)).2)) L) (closedBall x₀ RQ)) :
    let z := ((coordinateSplit i x₀).1, ((coordinateSplit i x₀).2,
      (coordinateSplit i (P.toFun c₀)).2))
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧ ∃ s > (0 : ℝ),
      closedBall c₀ (4 * s) ⊆ parameterInterior (2 * P.radius) ∧
    ∃ ρ > (0 : ℝ), ∃ g > (0 : ℝ), ∃ R > (0 : ℝ),
      let O := retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g R
      let D := retainedOpenIntegrationDomain z ε O
      let V := elapsedPhysicalBox z (ε / 2) ×ˢ ball c₀ (2 * s)
      IsOpen O ∧ Convex ℝ O ∧ IsCompact (closure O) ∧
      IsOpen D ∧ Convex ℝ D ∧ IsCompact (closure D) ∧
      IsOpen V ∧ Convex ℝ V ∧ IsCompact (closure V) ∧
      (primaryCoordinateChange i x₀, c₀) ∈ V ∧
      retainedAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture gap radius ⊆ O ∧
      (WithLp.prodContinuousLinearEquiv 2 ℝ E E ⁻¹'
        (closure (elapsedPhysicalBox z (ε / 2)) ×ˢ
          retainedAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture gap radius)) ⊆ D ∧
      closure O ⊆ retainedAnnularFrequencyCarrier ℓ z.2.2 ε (2 * aperture) g R ∧
      ∀ Q, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
        let X := (primaryCoordinateChange i).symm ⁻¹' ball (0 : E) T.physicalRadius
        let Ω := X ×ˢ ball c₀ (4 * s)
        IsOpen Ω ∧ Convex ℝ Ω ∧
        ContDiffOn ℝ ∞ (fun q ↦ T.primaryPhaseInCoordinates i Q q.1 q.2) Ω ∧
        ContDiffOn ℝ ∞ (fun q : E × Euclidean 3 ↦
          gradient (fun x ↦ T.primaryPhaseInCoordinates i Q x q.2) q.1) Ω ∧
        (∀ q ∈ X ×ˢ closedBall c₀ (4 * s),
          rootSuspension (fieldRoot (coordinateSplit i) Q.1 H)
            (q.1, gradient (fun x ↦ T.primaryPhaseInCoordinates i Q x q.2) q.1) = 0) ∧
        ∀ q ∈ closure (elapsedPhysicalBox z (ε / 2)) ×ˢ closedBall c₀ (2 * s),
          closedBall (WithLp.toLp 2
            (q.1, gradient (fun x ↦ T.primaryPhaseInCoordinates i Q x q.2) q.1))
            (4 * ρ) ⊆ D := by
  intro z
  have hphysical : MapsTo (primaryCoordinateChange i).symm
      (closure (elapsedPhysicalBox z ε)) (ball 0 T.physicalRadius) :=
    retained_primary_physical_buffer i z hεL (fun _ hw ↦ hKprimary (hrootPhysical hw))
  let θ₀ := primaryCoordinateChange i (P.toFun c₀)
  have hsp : spatialPart θ₀ = z.2.2 := by
    simp only [θ₀, z, primaryCoordinateChange_apply, spatialPart_timeSpacePoint]
  have hθ : θ₀ ∈ fullAngularCone ℓ z.2.2 (ε / 2) aperture := by
    refine ⟨?_, ?_⟩
    · change 0 < ℓ (spatialPart θ₀) ∧
        (ℓ (spatialPart θ₀))⁻¹ • spatialPart θ₀ ∈ ball z.2.2 (ε / 2)
      rw [hsp, hℓ]
      simpa only [inv_one, one_smul] using
        And.intro zero_lt_one (mem_ball_self (half_pos hε))
    · simpa only [θ₀, primaryCoordinateChange_apply, timeSpacePoint_time,
        spatialPart_timeSpacePoint, hℓ, mul_one] using hApθ
  obtain ⟨g, hg', R, hR, a, ha, hO, hOc, hOK, hFO, hθO, hOF⟩ :=
    exists_retained_open_annular_frequency_buffer ℓ z.2.2 (half_pos hε) hAp hg θ₀ hθ
      (by rw [hsp]; exact hℓ) (radius := radius)
  let O := retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g R
  obtain ⟨ρ, hρ, hmargin⟩ := exists_retained_integration_diagonal_margin z hε hO θ₀
    ((closedBall_subset_closedBall (by linarith : a ≤ 4 * a)).trans hθO)
  let N : Set (Coeff × E) :=
    (fun p ↦ primaryCoordinateChange i p.2) ⁻¹' ball θ₀ a
  have hN : IsOpen N := isOpen_ball.preimage
    ((primaryCoordinateChange i).continuous.comp continuous_snd)
  have hbase : (cubeStress (d + 1), P.toFun c₀) ∈ N := mem_ball_self ha
  obtain ⟨δ₁, hδ₁, hδ₁T, s₁, hs₁, hp₁, hpair⟩ :=
    T.exists_uniform_primary_pair_neighborhood hP hframe hc₀ hN hbase
  obtain ⟨δ₂, hδ₂, _, s₂, hs₂, _, hroot⟩ :=
    T.exists_uniform_retained_primary_root_domain hP hframe hc₀ hξ hr hL hμ hν hH
  let s := min s₁ s₂
  have hs : 0 < s := lt_min hs₁ hs₂
  have hs₁' : 4 * s ≤ 4 * s₁ := mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
  have hs₂' : 4 * s ≤ 4 * s₂ := mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
  have hparam : closedBall c₀ (4 * s) ⊆ parameterInterior (2 * P.radius) :=
    (closedBall_subset_closedBall hs₁').trans hp₁
  obtain ⟨hD, hDc, hDK, _⟩ := retainedOpenIntegrationDomain_geometry z ε hO hOc hOK
  have hVK : IsCompact (closure (elapsedPhysicalBox z (ε / 2) ×ˢ ball c₀ (2 * s))) := by
    rw [closure_prod_eq]
    exact (isCompact_closure_retained_physicalBox z ε).prod
      ((isCompact_closedBall c₀ (2 * s)).of_isClosed_subset isClosed_closure
        (closure_minimal ball_subset_closedBall isClosed_closedBall))
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, (min_le_left _ _).trans hδ₁T,
    s, hs, hparam, ρ, hρ, g, hg', R, hR, hO, hOc, hOK, hD, hDc, hDK,
    (isOpen_elapsedPhysicalBox _ _).prod isOpen_ball,
    (convex_elapsedPhysicalBox _ _).prod (convex_ball _ _), hVK, ?_,
    hFO, retained_annular_integration_subset z hε hFO, ?_, ?_⟩
  · refine ⟨?_, mem_ball_self (by positivity)⟩
    simp only [elapsedPhysicalBox, mem_ofPred_eq, primaryCoordinateChange_apply,
      timeSpacePoint_time, spatialPart_timeSpacePoint, z, coordinateSplit_fst]
    exact ⟨mem_ball_self (half_pos hε), mem_ball_self (half_pos hε)⟩
  · simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hOF
  · intro Q hQ X Ω
    obtain ⟨_, _, hφ, hgrad, heik⟩ := hroot Q (hQ.trans_le (min_le_right _ _))
    have hΩsub : Ω ⊆ X ×ˢ ball c₀ (4 * s₂) :=
      fun _ hq ↦ ⟨hq.1, ball_subset_ball hs₂' hq.2⟩
    refine ⟨(isOpen_ball.preimage (primaryCoordinateChange i).symm.continuous).prod
      isOpen_ball,
      ((convex_ball (0 : E) T.physicalRadius).linear_preimage
        (primaryCoordinateChange i).symm.toLinearMap).prod (convex_ball _ _),
      hφ.mono hΩsub, hgrad.mono hΩsub,
      fun q hq ↦ heik q ⟨hq.1, closedBall_subset_closedBall hs₂' hq.2⟩, ?_⟩
    intro q hq
    have hx : (primaryCoordinateChange i).symm q.1 ∈ ball 0 T.physicalRadius :=
      hphysical (closure_mono (show elapsedPhysicalBox z (ε / 2) ⊆ elapsedPhysicalBox z ε from
        fun _ hx ↦
        ⟨ball_subset_ball (by linarith : ε / 2 ≤ ε) hx.1,
          ball_subset_ball (by linarith : ε / 2 ≤ ε) hx.2⟩) hq.1)
    have hc : q.2 ∈ closedBall c₀ (4 * s) :=
      closedBall_subset_closedBall (by linarith) hq.2
    apply hmargin q.1 hq.1
    rw [T.primaryPhaseInCoordinates_gradient hP i Q hx (hparam hc)]
    exact ball_subset_closedBall (hpair Q (hQ.trans_le (min_le_left _ _)) _ hx _
      (closedBall_subset_closedBall hs₁' hc))

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
