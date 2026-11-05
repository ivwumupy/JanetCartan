module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FlowConic.LocalCharts
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FlowConic.CoefficientDomain
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.RefinedShell

/-!
# Supported shell geometry inside a prescribed coefficient neighborhood

Both outer radii are capped using the prescribed coefficient neighborhood.
The actual capped full-phase producer constructs the inverse and its image
buffers at these radii; the common conic balls are then chosen. Smaller original
masks and the additional frame threshold then precede the immersion. The actual
half-gap discharges the only conditional input of `exists_refined_supported_shell`.
This supplies actual supported shell geometry, independently of primitive
coefficient estimates and of the kernel adapter for the smaller masks.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.FlowConic
open CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison CanonicalCarrier ContinuumNormalReduction TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Actual supported normalized-shell containment, together with its SAME
outer local chart, augmented gap, input/output balls with a doubled output
buffer, punctured buffer and
the frequency bound `Cupper = 2`. The entire coefficient domain lies in the
prescribed open neighborhood `E`. Every radius and threshold precedes `F`.
The masks use `a'` and `r'`, while the phase and inverse retain `a` and `r`.
`exists_small_incidence_representative` permits `‖k‖ = 1/4` without changing
the selected direction, so the shell also satisfies `Cupper * ℓ ≤ 1`.
Consumer: `exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms`
(`app:ch_background:eq:bg-Psi`, `bg-full-complex-amplitude`). -/
theorem exists_actual_refined_supported_geometry_in_open {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {N : ℕ} {KF : Set (Euclidean n)} (hKF : IsCompact KF) (hKU : KF ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ KF)
    (C₀ : ℝ) {κmet κ : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ)
    {cap : ℝ} (hcap : 0 < cap)
    (E : Set (Euclidean n × CarrierParameter)) (hE : IsOpen E)
    (hcenter : ((0 : Euclidean n), (z₀ 0, spectatorCenter z₀)) ∈ E) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    let p₀ := augmentedInputCenter T (z₀ := z₀) (k := k)
    let q₀ := frozenAugmentedChart T p₀
    let G := FrozenIncidence.referenceEquiv T hP hz₀ hinc hd
    ∃ r > (0 : ℝ), ∃ a > (0 : ℝ), 6 * a < cap ∧
      coefficientDomain z₀ r (6 * a) ⊆ E ∧ 6 * a ≤ r ∧
      6 * a < T.family.radius ∧ 4 * a < 1 / 2 ∧
      (closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
        carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) ∧
    ∃ ρ > (0 : ℝ), ρ < cap ∧ closedBall p₀ ρ ⊆ symbolInputDomain z₀ ηb r (6 * a) ∧
    ∃ τ > (0 : ℝ), ∃ r' > (0 : ℝ), r' ≤ r ∧ r' ≤ ρ ∧
    ∃ a' > (0 : ℝ), a' ≤ a ∧ a' ≤ r' ∧ 4 * a' < ρ ∧
    ∃ δ > (0 : ℝ), ∃ cJ > (0 : ℝ), ∃ b > (0 : ℝ),
    ∃ V L : Set (ℝ × Euclidean (n - 1)),
      IsOpen V ∧ IsCompact (closure V) ∧ IsCompact L ∧ L ⊆ V ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm KF 4 F ≤ C₀ →
        (∀ x ∈ KF, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ KF, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (ProjectedStressFrame.projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (ProjectedStressFrame.projectedStress F - fun _ ↦ cubeStress n) < δ →
        let Q := ⟨ProjectedStressFrame.projectedStress F,
          contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
          (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)) ∧
        (∀ p ∈ physicalParameterSet z₀ (6 * a), ∀ u ∈ dataBox z₀ ηb (2 * r),
          ‖G.symm.toContinuousLinearMap.comp
            (fderiv ℝ (adaptedTransportChart T Q p) u) -
            ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2) ∧
        BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
          (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G ∧
        (∀ p ∈ physicalParameterSet z₀ (6 * a),
          ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
            ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖) ∧
        closedBall q₀ (2 * τ) ⊆ symbolDomain T Q z₀ ηb r (6 * a) ∧
        MapsTo (inverseCoordinates (symbolInverse T Q z₀ ηb r (6 * a)))
          (closedBall q₀ (2 * τ)) (closedBall p₀ ρ) ∧
        (∀ p ∈ closedBall p₀ ρ,
          ‖(augmentedReferenceEquiv T hP hz₀ hinc hd).symm.toContinuousLinearMap.comp
            (fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p) -
            ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
        (closure (augmentedTransportGradient (transportPosition T Q) '' conicMaskSupport z₀ ηb r' a') ∩
          {p | p.1.2.2 ≠ 0} ⊆ symbolDomain T Q z₀ ηb r (6 * a)) ∧
        (∀ x : Variables n, ‖x.2.2‖ = ‖k‖ → ∀ v : Euclidean 2,
          (x, v) ∈ closure (augmentedTransportGradient (transportPosition T Q) ''
            conicMaskSupport z₀ ηb r' a') → (x, v) ∈ closedBall q₀ τ) ∧
        (∀ p ∈ symbolDomain T Q z₀ ηb r (6 * a),
          ‖(symbolInverse T Q z₀ ηb r (6 * a) p).2‖ ≤ 2 * ‖p.1.2.2‖) := by
  dsimp only
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  have hηb : ηb ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc
  obtain ⟨ε, hε, hEcap⟩ := exists_coefficientDomain_cap z₀ E hE hcenter
  obtain ⟨r, hr, hrε, a, ha, hacap, har, haR, hphys, hcarrier, δ₀, hδ₀, cJ, hcJ,
    b, hb, V, L, hV, hVc, hLc, hLV, hlocal⟩ := exists_actual_local_charts_below T hP hz₀ hk hinc hd
      hKF hKU hball C₀ hκmet hκ (lt_min hcap (by norm_num : (0 : ℝ) < 1 / 2)) hε
  have hcell : 4 * a < 1 / 2 := by linarith [hacap.trans_le (min_le_right cap (1 / 2))]
  obtain ⟨δ₁, hδ₁, htrans⟩ := exists_supported_transverse_threshold T hP z₀ hηb hr hphys hcarrier
  obtain ⟨ρ, hρ, hρcap, hinput, τ₀, hτ₀, δ₂, hδ₂, hballs⟩ :=
    exists_common_conic_balls T hP hz₀ hk hinc hd hr ha hcap
  let τ := τ₀ / 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have htwo : 2 * τ = τ₀ := by dsimp [τ]; ring
  obtain ⟨r', hr', hrr, hrρ, a', ha', haa, har', haρ, δ₃, hδ₃, hshell⟩ :=
    exists_refined_supported_shell T hP hz₀ hk hinc hd hr ha hρ hτ
  refine ⟨r, hr, a, ha, hacap.trans_le (min_le_left _ _), hEcap hrε (har.trans hrε), har, haR, hcell, hcarrier,
    ρ, hρ, hρcap, hinput, τ, hτ, r', hr', hrr, hrρ, a', ha', haa, har', haρ,
    min (min δ₀ δ₁) (min δ₂ δ₃), lt_min (lt_min hδ₀ hδ₁) (lt_min hδ₂ hδ₃),
    cJ, hcJ, b, hb, V, L, hV, hVc, hLc, hLV, ?_⟩
  intro F hF hi hrank hlowF hmet hnormal hlow hclose
  let Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} :=
    ⟨ProjectedStressFrame.projectedStress F,
      contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank), hlow⟩
  obtain ⟨hf, hsliceGap, hInv, _⟩ := hlocal F hF hi hrank hlowF hmet hnormal hlow
    (hclose.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
  have htrans' : ∀ p ∈ physicalParameterSet z₀ (6 * a),
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖ := by
    intro p hp
    exact htrans Q (hclose.trans_le ((min_le_left _ _).trans (min_le_right _ _))) p
      ⟨ball_subset_ball har hp.1, ball_subset_ball har hp.2.1, ball_subset_ball har hp.2.2⟩
  obtain ⟨houtput, hrange, hgap⟩ := hballs Q
    (hclose.trans_le ((min_le_right _ _).trans (min_le_left _ _))) hf hInv htrans'
  have hbuffer := conicMaskImage_punctured_buffer T Q hηb hr ha (by linarith) htrans' hf
  have hsmall : closure (augmentedTransportGradient (transportPosition T Q) ''
      conicMaskSupport z₀ ηb r' a') ⊆
      closure (augmentedTransportGradient (transportPosition T Q) '' conicMaskSupport z₀ ηb r a) :=
    closure_mono (image_mono (conicMaskSupport_mono z₀ ηb hrr haa))
  exact ⟨hf, hsliceGap, hInv, htrans', by simpa only [htwo] using houtput,
    by simpa only [htwo] using hrange, hgap,
    fun _ hp ↦ hbuffer ⟨hsmall hp.1, hp.2⟩,
    hshell Q (hclose.trans_le ((min_le_right _ _).trans (min_le_right _ _))) hgap,
    fun _ hp ↦ symbolInverse_norm_le_two T Q hηb hr hInv htrans' hp⟩

end JanetCartan.ContinuumRow.FlowConic
