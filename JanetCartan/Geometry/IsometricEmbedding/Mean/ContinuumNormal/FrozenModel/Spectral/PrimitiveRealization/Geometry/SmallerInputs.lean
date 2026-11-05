module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Construction

/-!
# Smaller frozen conic inputs with prescribed caps

The smaller masks in the primitive realization need their own canonical inverse.
This construction uses the capped annular inverse producer and the actual
transverse threshold. Both radii and the threshold precede the current frame.
Consumer: `frozenMeasured_fullReflectedMatrixAmplitude_eq_canonical_of_enlargement`
and the supported carrier constructor (`new:lem:scaling`,
`app:ch_background:prop:bg-frame`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open ContinuumNormalReduction.TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

private theorem pullback_smaller_local_geometry
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


/-- Construct the smaller local inverse below arbitrary positive radius and
physical caps. Thus taking the caps below the outer radii, input radius and
output radius proves every required shrinking inequality. No existence of a
smaller inverse or transverse estimate is assumed. The local analytic outputs
are the same as those of `exists_frozen_conic_inputs`, with the additional
radius cap needed by inverse enlargement (`new:lem:scaling`, `bg-Psi`). -/
theorem exists_smaller_frozen_conic_inputs {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {rmax amax : ℝ} (hrmax : 0 < rmax) (hamax : 0 < amax) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    let G := FrozenIncidence.referenceEquiv T hP hz₀ hinc hd
    ∃ r' > (0 : ℝ), r' ≤ rmax ∧ ∃ a' > (0 : ℝ), 6 * a' < amax ∧ 6 * a' ≤ r' ∧
      6 * a' < T.family.radius ∧ 3 * r' < T.family.radius / 8 ∧
      (closedBall (spectatorCenter z₀) (3 * r') ×ˢ closedBall (z₀ 0) (3 * r') ⊆
        carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) ∧
    ∃ δ > (0 : ℝ), ∃ cJ > (0 : ℝ), ∃ b > (0 : ℝ),
    ∃ V L : Set (ℝ × Euclidean (n - 1)),
      IsOpen V ∧ IsCompact (closure V) ∧ IsCompact L ∧ L ⊆ V ∧
      ∀ Q,
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress n) < δ →
        ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
          (physicalParameterSet z₀ (6 * a') ×ˢ dataSet z₀ ηb (3 * r')) ∧
        (∀ p ∈ physicalParameterSet z₀ (6 * a'), ∀ u ∈ dataBox z₀ ηb (2 * r'),
          ‖G.symm.toContinuousLinearMap.comp
            (fderiv ℝ (adaptedTransportChart T Q p) u) -
            ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2) ∧
        BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a'))
          (dataBox z₀ ηb r') (dataSet z₀ ηb (2 * r')) (dataBox z₀ ηb (2 * r')) V L b cJ G ∧
        (∀ p ∈ physicalParameterSet z₀ (6 * a'),
          ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r' (angularWidth ηb r'),
            ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r' / 4) * ‖u.2‖) := by
  dsimp only
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  have hηb : ηb ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc
  obtain ⟨r', hr', hrr, s, hs, hsr, hphys, hcarrier, e, he, δ₀, hδ₀,
    cJ, hcJ, b, hb, V, L, cT, hcT, bT, hbT, VT, LT, A, hA, B, hB,
    hV, hVc, hLc, hLV, hVT, hVTc, hLTc, hLTV, hcharts⟩ :=
    ActualInverses.exists_actual_buffered_inverses_below T hP hz₀ hk hinc hd hrmax
  let a' := min s amax / 12
  have ha' : 0 < a' := by dsimp [a']; positivity
  have has : 6 * a' < s := by dsimp [a']; linarith [min_le_left s amax]
  have hacap : 6 * a' < amax := by dsimp [a']; linarith [min_le_right s amax]
  have har : 6 * a' ≤ r' := has.le.trans hsr
  obtain ⟨δ₁, hδ₁, htrans⟩ :=
    exists_supported_transverse_threshold T hP z₀ hηb hr' hphys hcarrier
  refine ⟨r', hr', hrr, a', ha', hacap, har,
    by linarith [T.family.radius_pos], hphys, hcarrier,
    min δ₀ δ₁, lt_min hδ₀ hδ₁, cJ, hcJ, b, hb, V, L, hV, hVc, hLc, hLV, ?_⟩
  intro Q hQ
  obtain ⟨hf, _, hgap, _, hInv, _, _, _, hann⟩ :=
    hcharts Q (hQ.trans_le (min_le_left _ _))
  obtain ⟨hf', hgap', hInv', _⟩ := pullback_smaller_local_geometry T Q z₀ ηb he has
    V L _ hf hgap hInv (fun p hp u hu ↦ (hann p hp u hu).1)
  refine ⟨hf', hgap', hInv', ?_⟩
  intro p hp
  exact htrans Q (hQ.trans_le (min_le_right _ _)) p
    ⟨ball_subset_ball har hp.1, ball_subset_ball har hp.2.1, ball_subset_ball har hp.2.2⟩

end JanetCartan.ContinuumNormal.FrozenModel
