module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.ChartMap

/-!
# Buffered carrier charts with an incidence-radius cap

The capped actual Hamilton inverse producer constructs fresh image buffers at
the chosen incidence radius. Specializing it to the projected stress retains
the same Hamilton family and canonical phase. No old inverse is restricted.
The physical pullback keeps its input domain unchanged, so inverse agreement
is exactly `phaseChartInverse_adaptedTransportChart`.

Consumer: `FlowConic.exists_actual_refined_supported_geometry_in_open`, for
`app:ch_background:eq:bg-Psi`, `bg-jacobian`, and `bg-mixed-input`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.FlowConic
open CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison CanonicalCarrier
variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

private theorem pullback_local_geometry
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) {r s a e cJ b : ℝ}
    (he : 0 < e) (has : 6 * a < s) (V L : Set (ℝ × Euclidean (n - 1)))
    (G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1)))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (fullChartFamily (current T Q) (spatialCarrier T)))
      (fullParameterSet z₀ s (2 * e) ×ˢ dataSet z₀ ηb (3 * r)))
    (hgap : ∀ p ∈ fullParameterSet z₀ s (2 * e), ∀ u ∈ dataBox z₀ ηb (2 * r),
      ‖(G.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp
        (fderiv ℝ (fullChartFamily (current T Q) (spatialCarrier T) p) u) -
        ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2)
    (hInv : BufferedPhaseInverse (fullChartFamily (current T Q) (spatialCarrier T))
      (fullParameterSet z₀ s (2 * e))
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (hann : ∀ p ∈ fullParameterSet z₀ s (2 * e), ∀ u ∈ dataBox z₀ ηb (2 * r),
      ‖(fullChartFamily (current T Q) (spatialCarrier T) p u).2 - u.2‖ ≤ ‖u.2‖ / 2) :
    ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)) ∧
    (∀ p ∈ physicalParameterSet z₀ (6 * a), ∀ u ∈ dataBox z₀ ηb (2 * r),
      ‖(G.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp
        (fderiv ℝ (adaptedTransportChart T Q p) u) -
        ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2) ∧
    BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G ∧
    (∀ p ∈ physicalParameterSet z₀ (6 * a), ∀ u ∈ dataBox z₀ ηb (2 * r),
      ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ ‖u.2‖ / 2) := by
  have hp : MapsTo (phaseParameters T) (physicalParameterSet z₀ (6 * a))
      (fullParameterSet z₀ s (2 * e)) :=
    fun _ h ↦ phaseParameters_mem T (by positivity) has.le h
  have heq : adaptedTransportChart T Q = fun p ↦
      fullChartFamily (current T Q) (spatialCarrier T) (phaseParameters T p) := by
    funext p u
    exact adaptedTransportChart_eq T Q p u
  have hinv : Function.uncurry (phaseChartInverse (adaptedTransportChart T Q)
      (dataSet z₀ ηb (2 * r))) =
      fun q ↦ phaseChartInverse (fullChartFamily (current T Q) (spatialCarrier T))
        (dataSet z₀ ηb (2 * r))
        (phaseParameters T q.1) q.2 := by
    funext q
    exact phaseChartInverse_adaptedTransportChart T Q _ _ _
  have harg : ContDiff ℝ ∞ (fun q : (Euclidean 2 × Euclidean n × Euclidean n) ×
      (ℝ × Euclidean (n - 1)) ↦ (phaseParameters T q.1, q.2)) :=
    ((phaseParameters_smooth T).comp contDiff_fst).prodMk contDiff_snd
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heq]
    apply hf.comp (s := physicalParameterSet z₀ (6 * a) ×ˢ
      dataSet z₀ ηb (3 * r)) harg.contDiffOn
    exact fun q hq ↦ ⟨hp hq.1, hq.2⟩
  · intro p hpp u hu
    rw [heq]
    exact hgap _ (hp hpp) u hu
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hinv]
      apply hInv.smooth.comp (s := physicalParameterSet z₀ (6 * a) ×ˢ V) harg.contDiffOn
      exact fun q hq ↦ ⟨hp hq.1, hq.2⟩
    · intro p hpp
      rw [heq]
      exact hInv.injective _ (hp hpp)
    · intro p hpp u hu v hv
      rw [heq]
      exact hInv.lower _ (hp hpp) u hu v hv
    · intro p hpp
      rw [heq]
      exact hInv.image_subset _ (hp hpp)
    · intro p hpp
      rw [heq]
      exact hInv.inner_buffer _ (hp hpp)
    · intro p hpp
      rw [heq]
      exact hInv.outer_buffer _ (hp hpp)
    · intro p hpp v hv
      rw [phaseChartInverse_adaptedTransportChart]
      exact hInv.inverse_mem _ (hp hpp) v hv
    · intro p hpp v hv
      rw [phaseChartInverse_adaptedTransportChart, heq]
      exact hInv.right_inv _ (hp hpp) v hv
    · intro p hpp u hu
      rw [phaseChartInverse_adaptedTransportChart, heq]
      exact hInv.left_inv _ (hp hpp) u hu
    · intro p hpp u hu
      rw [heq]
      exact hInv.differential_bounds _ (hp hpp) u hu
  · intro p hpp u hu
    rw [heq]
    exact hann _ (hp hpp) u hu


/-- The actual local carrier charts, constructed from primitive projected
stress hypotheses with all domains and thresholds preceding `F`. The radius
`a` leaves room for the physical cutoff support at `4a` and a coefficient
buffer at `6a`; `r` also obeys a separately prescribed cap. The actual capped
full-phase constructor proves all image buffers at this new radius, before
`F`, and is specialized to its projected stress. No successful chart is assumed.
Source: `app:ch_background:eq:bg-Psi`, `app:ch_background:eq:bg-jacobian`. -/
theorem exists_actual_local_charts_below {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {N : ℕ} {KF : Set (Euclidean n)} (_hKF : IsCompact KF) (_hKU : KF ⊆ U)
    (_hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ KF)
    (C₀ : ℝ) {κmet κ : ℝ} (_hκmet : 0 < κmet) (_hκ : 0 < κ)
    {cap rcap : ℝ} (hcap : 0 < cap) (hrcap : 0 < rcap) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    let G := FrozenIncidence.referenceEquiv T hP hz₀ hinc hd
    ∃ r > (0 : ℝ), r ≤ rcap ∧ ∃ a > (0 : ℝ), 6 * a < cap ∧ 6 * a ≤ r ∧
      6 * a < T.family.radius ∧ 3 * r < T.family.radius / 8 ∧
      (closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
        carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) ∧
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
          ‖(G.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp
            (fderiv ℝ (adaptedTransportChart T Q p) u) -
              ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2) ∧
        BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
          (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r))
          V L b cJ G ∧
        (∀ p ∈ physicalParameterSet z₀ (6 * a), ∀ u ∈ dataBox z₀ ηb (2 * r),
          ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ ‖u.2‖ / 2) := by
  dsimp only
  obtain ⟨r, hr, hrcap', s, hs, hsr, hphys, hcarrier, e, he, _, δ, hδ,
    cJ, hcJ, b, hb, V, L, cT, hcT, bT, hbT, VT, LT, A, hA, B, hB,
    hV, hVc, hLc, hLV, hVT, hVTc, hLTc, hLTV, hcharts⟩ :=
    ActualInverses.exists_actual_buffered_inverses_with_caps T hP hz₀ hk hinc hd
      hrcap (show (0 : ℝ) < 1 by norm_num)
  let a := min s cap / 12
  have ha : 0 < a := div_pos (lt_min hs hcap) (by norm_num)
  have has : 6 * a < s := by dsimp [a]; linarith [min_le_left s cap]
  have hacap : 6 * a < cap := by dsimp [a]; linarith [min_le_right s cap]
  have har : 6 * a ≤ r := by linarith
  have haR : 6 * a < T.family.radius := by linarith [T.family.radius_pos]
  refine ⟨r, hr, hrcap', a, ha, hacap, har, haR, hphys, hcarrier, δ, hδ, cJ, hcJ, b, hb,
    V, L, hV, hVc, hLc, hLV, ?_⟩
  intro F hF hi hrank _hlowF _hmet _hnormal hlow hclose
  let Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} :=
    ⟨ProjectedStressFrame.projectedStress F,
      contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank), hlow⟩
  obtain ⟨hf, _, hgap, _, hInv, _, _, _, hann⟩ :=
    hcharts Q hclose
  exact pullback_local_geometry T Q z₀ _ he has V L _ hf hgap hInv
    (fun p hp u hu ↦ (hann p hp u hu).1)

end JanetCartan.ContinuumRow.FlowConic
