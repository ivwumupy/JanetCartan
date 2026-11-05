module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.UnitRealization.Support
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.UniformConic.LocalCharts
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FlowConic.CoefficientDomain
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.RefinedShell

/-!
# One retained geometry for the current and frozen carriers

Replay the retained local radius selection, capping its output ball by the
input radius and its single mask choice by that output radius. The original
current outputs are retained in their original order, followed by the frozen
inverse range, half-gap, supported shell and punctured buffer on the SAME
inner masks and OUTER inverse. No finite cover has yet been selected.
Consumer: `exists_joint_carrier_normal_geometry_with_unit`.
Sources: `app:ch_background:eq:bg-Psi`, `app:ch_background:eq:bg-full-complex-amplitude`,
`new:lem:scaling`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.RetainedFrozen.UnitRealization
open ContinuumRow UniformConic CanonicalConic FlowConic FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison CanonicalCarrier ContinuumNormalReduction TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Choose the actual local chart, augmented gap, input/output balls, doubled
output buffer, punctured buffer and refined supported shell before the geometric
budgets. The entire coefficient domain lies in the prescribed open `E`.
The masks use `a'` and `r'`; the SAME phase and inverse retain `a` and `r`.
The frequency bound remains `Cupper = 2`.
Consumer: `exists_actual_supported_carrier_in_open_before_geometry_of_primitive_controls`.
Sources: `app:ch_background:eq:bg-Psi`, `bg-full-complex-amplitude`,
`new:sec:order-of-choices` (paper-v2.tex). -/
theorem exists_retained_joint_supported_geometry {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {N : ℕ}
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
          ‖(symbolInverse T Q z₀ ηb r (6 * a) p).2‖ ≤ 2 * ‖p.1.2.2‖) ∧
        (closedBall q₀ (2 * τ) ⊆ frozenSymbolDomain T Q z₀ ηb r (6 * a) ∧
        MapsTo (inverseCoordinates (frozenSymbolInverse T Q z₀ ηb r (6 * a)))
          (closedBall q₀ (2 * τ)) (closedBall p₀ ρ) ∧
        (∀ p ∈ closedBall p₀ ρ,
          ‖(augmentedReferenceEquiv T hP hz₀ hinc hd).symm.toContinuousLinearMap.comp
            (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition T Q 0)) p) -
            ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
        (∀ x : Variables n, ‖x.2.2‖ = ‖k‖ → ∀ v : Euclidean 2,
          (x, v) ∈ closure (augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
            conicMaskSupport z₀ ηb r' a') → (x, v) ∈ closedBall q₀ τ) ∧
        (closure (augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
          conicMaskSupport z₀ ηb r' a') ∩ {p | p.1.2.2 ≠ 0} ⊆
          frozenSymbolDomain T Q z₀ ηb r (6 * a))) := by
  dsimp only
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  have hηb : ηb ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc
  obtain ⟨ε, hε, hEcap⟩ := exists_coefficientDomain_cap z₀ E hE hcenter
  obtain ⟨r, hr, hrε, a, ha, hacap, har, haR, hphys, hcarrier, δ₀, hδ₀, cJ, hcJ,
    b, hb, V, L, hV, hVc, hLc, hLV, hlocal⟩ := exists_actual_local_charts_below_before_geometry T hP hz₀ hk hinc hd (lt_min hcap (by norm_num : (0 : ℝ) < 1 / 2)) hε
  have hcell : 4 * a < 1 / 2 := by linarith [hacap.trans_le (min_le_right cap (1 / 2))]
  obtain ⟨δ₁, hδ₁, htrans⟩ := exists_supported_transverse_threshold T hP z₀ hηb hr hphys hcarrier
  obtain ⟨ρ, hρ, hρcap, hinput, τ₀, hτ₀, δ₂, hδ₂, hballs⟩ :=
    exists_common_conic_balls T hP hz₀ hk hinc hd hr ha hcap
  let τ := min τ₀ ρ / 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have htτ : 2 * τ ≤ τ₀ := by dsimp [τ]; linarith [min_le_left τ₀ ρ]
  have htρ : 2 * τ ≤ ρ := by dsimp [τ]; linarith [min_le_right τ₀ ρ]
  have hmaskcap : 0 < min a (τ / 8) := lt_min ha (by positivity)
  obtain ⟨r', hr', hrr, hrρ, a', ha', haaCap, har', haρ, δ₃, hδ₃, hshell⟩ :=
    exists_refined_supported_shell T hP hz₀ hk hinc hd hr hmaskcap hρ hτ
  have haa : a' ≤ a := haaCap.trans (min_le_left _ _)
  have haτ : 4 * a' ≤ τ := by linarith [haaCap.trans (min_le_right _ _)]
  refine ⟨r, hr, a, ha, hacap.trans_le (min_le_left _ _), hEcap hrε (har.trans hrε), har, haR, hcell, hcarrier,
    ρ, hρ, hρcap, hinput, τ, hτ, r', hr', hrr, hrρ, a', ha', haa, har', haρ,
    min (min δ₀ δ₁) (min δ₂ δ₃), lt_min (lt_min hδ₀ hδ₁) (lt_min hδ₂ hδ₃),
    cJ, hcJ, b, hb, V, L, hV, hVc, hLc, hLV, ?_⟩
  intro F hF hi hrank hlow hclose
  let Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} :=
    ⟨ProjectedStressFrame.projectedStress F,
      contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank), hlow⟩
  obtain ⟨hf, hsliceGap, hInv, _⟩ := hlocal F hF hi hrank hlow
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
  have houtput' := (closedBall_subset_closedBall htτ).trans houtput
  have hrange' := hrange.mono_left (closedBall_subset_closedBall htτ)
  have hcenterEq := frozenAugmentedChart_center T hP hz₀ hinc
  have houtput0 := houtput'
  have hrange0 := hrange'
  rw [hcenterEq] at houtput0 hrange0
  have hfrozen := frozenInverse_common_ball T Q htρ houtput0
    (by simpa only [augmentedInputCenter] using hrange0)
  have hshell' := hshell Q
    (hclose.trans_le ((min_le_right _ _).trans (min_le_right _ _))) hgap
  refine ⟨hf, hsliceGap, hInv, htrans', houtput', hrange', hgap,
    fun _ hp ↦ hbuffer ⟨hsmall hp.1, hp.2⟩,
    hshell', (fun _ hp ↦ symbolInverse_norm_le_two T Q hηb hr hInv htrans' hp),
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcenterEq]
    exact hfrozen.1
  · rw [hcenterEq]
    simpa only [augmentedInputCenter] using hfrozen.2
  · exact frozenAugmented_halfGap_of_original T Q hP hr (by linarith) hcarrier
      hz₀ hinc hd hηb hinput hf hgap
  · intro x hx v hv
    have hh := retainedFrozenMaskImage_supported_shell T Q hP hηb hr ha
      (by linarith) hcarrier ha' hrr haa (k := k) (ℓ := ‖k‖) (τ := τ) (p := (x, v)) haτ
      (fun q hq hmem ↦ by
        have hh := hshell' q.1 hq q.2 hmem
        rw [hcenterEq] at hh
        exact hh) hx hv
    rw [hcenterEq]
    exact hh
  · exact frozenRefinedMaskImage_punctured_buffer T Q hP hηb hr ha
      (by linarith) hcarrier hf htrans' hrr haa

end JanetCartan.ContinuumNormal.RetainedFrozen.UnitRealization
