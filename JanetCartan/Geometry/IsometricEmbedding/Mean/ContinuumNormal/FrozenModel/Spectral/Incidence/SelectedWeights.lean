module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Incidence.RootGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Incidence.Weights
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualGaps

/-!
# Positive weights at the same constructed roots

This is the local incidence construction consumed by the finite spectral
assembly in `app:ch_background:prop:bg-frame`. A fixed adjugate entry is chosen
before the frame. Explicit smaller frequency and root-error neighborhoods keep
that entry valid for the SAME roots of `app:ch_seed:eq:seed-actual-detection`.
The pivot, normal, masks, input covector and inverse point are proved here;
the buffered inverse inputs retain their producer `exists_frozen_conic_inputs`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic
open ContinuumNormalReduction TransportSymbol ConicChart
open NullTransport ProjectedStressFrame

private theorem constructed_incidence_minor_neighborhood {n : ℕ} {D : CoverData n}
    {c₀ C₀ : ℝ} (hD : D.IsValid c₀ C₀) {R : IncidenceRefinement D} (hR : R.IsValid)
    (j : Fin R.chartCount) (a : Fin (D.patchCount (R.sourceChart j)))
    {κ₀ : Euclidean n} (hκ₀ : κ₀ ∈ ball (R.center j) (2 * R.radius j))
    {W : Set (Euclidean 3)} (hW : IsOpen W) (hzW : D.roots (R.sourceChart j) a κ₀ ∈ W)
    {c εmax : ℝ} (hc : 0 < c) (hemax : 0 < εmax) :
    ∃ ρ ε₀ : ℝ, 0 < ρ ∧ 0 < ε₀ ∧ ε₀ ≤ εmax ∧
      ∀ {s B ε : ℝ}, 0 < s → ε ≤ ε₀ →
      ∀ (Q : Euclidean n → Fin n → MetricTensor n)
        (Θ : (b : Fin D.chartCount) → Fin (D.patchCount b) → Euclidean n → Euclidean 3 → ℝ)
        (g : (j : Fin R.chartCount) → Fin (D.patchCount (R.sourceChart j)) →
          Euclidean n × Euclidean n → ℝ),
      IsConstructedIncidenceRootFamily D R s c B ε Q Θ g →
      ∀ κ ∈ ball κ₀ ρ,
        incidenceParameter (D.roots (R.sourceChart j) a (R.center j)) (g j a (0, κ)) ∈ W := by
  obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.mp hW _ hzW
  have hdom := hR.2.1 j (ball_subset_closedBall hκ₀)
  have hroot : ContinuousAt (D.roots (R.sourceChart j) a) κ₀ :=
    (hD.2.2.2.2.1 (R.sourceChart j) a).2.1.continuousOn.continuousAt
      ((hD.2.2.1 _).mem_nhds hdom)
  have hnear : ∀ᶠ κ in 𝓝 κ₀,
      κ ∈ ball (R.center j) (2 * R.radius j) ∧
        dist (D.roots (R.sourceChart j) a κ) (D.roots (R.sourceChart j) a κ₀) < e / 2 :=
    Filter.Eventually.and (isOpen_ball.mem_nhds hκ₀) (hroot (ball_mem_nhds _ (half_pos he)))
  obtain ⟨ρ, hρ, hnear⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨ρ, min εmax (c * (e / 2)), hρ, lt_min hemax (by positivity), min_le_left _ _, ?_⟩
  intro s B ε hs hε Q Θ g hg κ hκ
  have hp : (0, κ) ∈ ball (0 : Euclidean n) (3 * s) ×ˢ
      ball (R.center j) (2 * R.radius j) :=
    ⟨by simpa using (show 0 < 3 * s by positivity), (hnear hκ).1⟩
  have herr := ((hg j a).2.2.1 (0, κ) hp).2.2.2.2.2.2.1
  have heps : ε / c ≤ e / 2 := (div_le_iff₀ hc).mpr (by
    simpa only [mul_comm] using hε.trans (min_le_right _ _))
  apply hball
  rw [mem_ball]
  exact (dist_triangle _ (D.roots (R.sourceChart j) a κ) _).trans_lt
    (show dist _ (D.roots (R.sourceChart j) a κ) +
      dist (D.roots (R.sourceChart j) a κ) (D.roots (R.sourceChart j) a κ₀) < e from by
        rw [dist_eq_norm]
        linarith [(hnear hκ).2])

/-- For every nonzero reference frequency, choose a fixed null-column minor,
a frequency neighborhood, a smaller root tolerance and a primitive frame
threshold. At every SAME constructed root in that neighborhood, the explicit
input covector solves the frequency equation, the ORIGINAL angular mask is one,
the EXACT canonical inverse recovers the root, the reduced coefficient is its
actual detector, and the literal weight is strictly positive above the geometric
frequency threshold (`app:ch_background:prop:bg-frame`,
`app:ch_seed:eq:seed-actual-detection`).

`exists_actual_null_gaps` produces both pivot and minor; the normal threshold is
`exists_canonicalFrozen_weight_threshold`. The root producer is the last clause
of `exists_constructed_incidence_roots`, applied at the returned smaller positive
`ε₀` (or a finite minimum). The retained inverse hypotheses are exactly those
produced by `exists_frozen_conic_inputs`. Finite coverage and one common root
family remain the parent's assembly; no coverage is inferred from shrinking.
-/
theorem exists_constructed_incidence_positive_weights {n : ℕ} (hn : 5 ≤ n)
    {D : CoverData n} {c₀ C₀ : ℝ} (hD : D.IsValid c₀ C₀)
    {R : IncidenceRefinement D} (hR : R.IsValid)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    (j : Fin R.chartCount) (a : Fin (D.patchCount (R.sourceChart j)))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n)
      (T ⟨R.sourceChart j, a⟩).data.localReference.stateRadius ⊆ K)
    (M : ℝ) {κ₀ : Euclidean n}
    (hκ₀ : κ₀ ∈ ball (R.center j) (2 * R.radius j)) (hκ₀ne : κ₀ ≠ 0)
    {r a₀ c εmax : ℝ} (hr : 0 < r) (ha : 0 < a₀) (hc : 0 < c) (hemax : 0 < εmax) :
    let T₀ := T ⟨R.sourceChart j, a⟩
    let z₀ := D.roots (R.sourceChart j) a κ₀
    let ηb := T₀.data.adapted.embedding.toContinuousLinearMap.adjoint κ₀
    ∃ hηb : ηb ≠ 0, ∃ row col : Fin n, ∃ ρ ε₀ δ : ℝ,
      0 < ρ ∧ 0 < ε₀ ∧ ε₀ ≤ εmax ∧ ε₀ / c ≤ a₀ / 8 ∧ 0 < δ ∧
      ∀ {s B ε : ℝ}, 0 < s → ε ≤ ε₀ →
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n))
        (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      cNorm K 4 F ≤ M →
      cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < δ →
      ∀ (hlow : ∀ i, cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < (T i).family.threshold)
        (g : (j : Fin R.chartCount) → Fin (D.patchCount (R.sourceChart j)) →
          Euclidean n × Euclidean n → ℝ),
      let hQ := contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
      let Q₀ := ⟨projectedStress F, hQ, hlow ⟨R.sourceChart j, a⟩⟩
      IsConstructedIncidenceRootFamily D R s c B ε (projectedStress F)
        (fun j a ↦ (T ⟨j, a⟩).carrier ⟨projectedStress F, hQ, hlow ⟨j, a⟩⟩) g →
      ∀ {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
        {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))},
      6 * a₀ ≤ 3 * r →
      (closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
        carrierParameters ⁻¹' parameterInterior (3 * (D.patches (R.sourceChart j) a).radius / 2)) →
      ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T₀ Q₀))
        (physicalParameterSet z₀ (6 * a₀) ×ˢ dataSet z₀ ηb (3 * r)) →
      BufferedPhaseInverse (adaptedTransportChart T₀ Q₀) (physicalParameterSet z₀ (6 * a₀))
        (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G →
      (∀ p ∈ physicalParameterSet z₀ (6 * a₀),
        ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
          ‖(adaptedTransportChart T₀ Q₀ p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖) →
      (∀ p ∈ physicalParameterSet z₀ (6 * a₀), ∀ u ∈ dataBox z₀ ηb (2 * r),
        ‖(G.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp
          (fderiv ℝ (adaptedTransportChart T₀ Q₀ p) u) -
            ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2) →
      0 < cJ →
      ∀ κ ∈ ball κ₀ ρ, ∀ t > (0 : ℝ), frozenHighFrequencyRadius T₀ G ≤ ‖t • κ‖ →
      ∀ (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
        (initial : Euclidean (n - 1) × Euclidean 3 → ℝ),
      let z := incidenceParameter (D.roots (R.sourceChart j) a (R.center j)) (g j a (0, κ))
      let η := t • T₀.data.adapted.embedding.toContinuousLinearMap.adjoint κ
      let p : InputVariables n := ((0, 0), (z 0, spectatorCenter z₀), η)
      let out := ((0, 0, t • κ), spectatorCenter z₀)
      let u := frozenSymbolInverse T₀ Q₀ z₀ ηb r (6 * a₀)
      let angular := angularMask z₀ (NormedSpace.normalize ηb) ha (angularWidth_spec hηb hr).1
      let coeff := uncutFrozenCoefficients T₀ Q₀ F row col Φ Y initial angular FixedCutoffs.highFrequency
      1 / 2 ≤ initial (Y (0, (0, z))) →
      transportAveragedGradient (normalizedTransportPosition T₀ Q₀ 0) p = t • κ ∧
      p ∈ frozenInputDomain z₀ ηb r (6 * a₀) ∧
      out ∈ frozenSymbolDomain T₀ Q₀ z₀ ηb r (6 * a₀) ∧
      u out = (z 0, η) ∧ parameter ((u out).1, out.2) = z ∧
      angular ((u out).1, out.2) (‖(u out).2‖⁻¹ • (u out).2) = 1 ∧
      coeff.reduced (0, ((u out).1, out.2)) = quadratic (projectedStress F 0) (T₀.carrierGradient Q₀ 0 z) ∧
      0 < inputWeight coeff (transportAbsoluteJacobian (adaptedSliceCoordinates T₀)
        (normalizedTransportPosition T₀ Q₀ 0)) (inverseCoordinates u out) := by
  dsimp only
  let T₀ := T ⟨R.sourceChart j, a⟩
  have hP := (hD.2.2.2.2.1 (R.sourceChart j) a).1
  obtain ⟨dnull, μ, pivot, hdnull, hμ, hpivot, W, hW, hcover, hnull⟩ :=
    exists_actual_null_gaps (by omega : 2 ≤ n) hP T₀ hK hKU hball
  have hz₀ := (hD.2.2.2.2.1 (R.sourceChart j) a).2.2.1 κ₀
    (hR.2.1 j (ball_subset_closedBall hκ₀))
  obtain ⟨row, hrow⟩ := mem_iUnion.mp (hcover (fun i ↦ (hz₀.1 i).le))
  obtain ⟨col, hcol⟩ := mem_iUnion.mp hrow
  obtain ⟨ρm, εm, hρm, hεm, hεmax, hminor⟩ :=
    constructed_incidence_minor_neighborhood hD hR j a hκ₀ (hW row col) hcol hc hemax
  obtain ⟨hηb, ρp, εp, hρp, hεp, hεpm, hec, hplace⟩ :=
    exists_constructed_incidence_plateau_tolerance hD hR T j a hκ₀ hκ₀ne hr ha hc hεm
  obtain ⟨dw, hdw, hweight⟩ := exists_canonicalFrozen_weight_threshold hn hP T₀ hK hKU hball M hμ
  refine ⟨hηb, row, col, min ρm ρp, εp, min dnull dw,
    lt_min hρm hρp, hεp, hεpm.trans hεmax, hec, lt_min hdnull hdw, ?_⟩
  intro s B ε hs hε F hF hi hrank hM hclose hlow g hg b cJ V L G
    har hcarrier hf hInv htrans hgap hcJ κ hκ t ht hk Φ Y initial hi₀
  let Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T₀.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T₀.family.threshold} :=
    ⟨projectedStress F, contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank),
      hlow ⟨R.sourceChart j, a⟩⟩
  let z := incidenceParameter (D.roots (R.sourceChart j) a (R.center j)) (g j a (0, κ))
  let z₀ := D.roots (R.sourceChart j) a κ₀
  let ηb := T₀.data.adapted.embedding.toContinuousLinearMap.adjoint κ₀
  let η := t • T₀.data.adapted.embedding.toContinuousLinearMap.adjoint κ
  let out : Variables n × Euclidean 2 := ((0, 0, t • κ), spectatorCenter z₀)
  let u := frozenSymbolInverse T₀ Q₀ z₀ ηb r (6 * a₀)
  let angular := angularMask z₀ (NormedSpace.normalize ηb) ha (angularWidth_spec hηb hr).1
  have hκm := ball_subset_ball (min_le_left ρm ρp) hκ
  have hκp := ball_subset_ball (min_le_right ρm ρp) hκ
  obtain ⟨hκchart, hη, hθ, hzplateau, hv, _⟩ := hplace hs hε _ _ g hg κ hκp
  have hroot := (hg j a).2.2.1 (0, κ)
    ⟨by simpa using (show 0 < 3 * s by positivity), hκchart⟩
  have hz : z ∈ parameterCube (3 * (D.patches (R.sourceChart j) a).radius / 2) :=
    fun i ↦ (hroot.2.1 i).le.trans (by linarith [hP.1])
  have hzW := hminor hs (hε.trans hεpm) _ _ g hg κ hκm
  obtain ⟨hpiv, hmin⟩ := hnull Q₀ (hclose.trans_le (min_le_left _ _)) 0
    (by simpa using T₀.physicalRadius_pos)
    (hball (mem_closedBall_self T₀.data.localReference.stateRadius_pos.le)) z hz
  have hpiv' := ne_of_gt (hpivot.trans_le hpiv)
  have hinc : fderiv ℝ (determinant (Q₀.1 0)) (T₀.carrierGradient Q₀ 0 z) κ = 0 :=
    hroot.2.2.2.2.1
  obtain ⟨hforward, hpin, hout, hinv, hmask⟩ := frozen_tangent_plateau_inverse T₀ Q₀ hP
    hηb hr ha har hcarrier hInv htrans hz hpiv' hinc hη hzplateau hv hθ ht
  change u out = (z 0, η) at hinv
  have hparam : parameter ((u out).1, out.2) = z := by
    rw [hinv]
    change parameter (z 0, spectatorCenter (D.roots (R.sourceChart j) a κ₀)) = z
    rw [← hv, parameter_apply, carrierParameters_spectatorCenter]
  have hmask' : angular ((u out).1, out.2) (‖(u out).2‖⁻¹ • (u out).2) = 1 := by
    rw [hinv]; exact hmask
  refine ⟨hforward, hpin, hout, hinv, hparam, hmask', ?_, ?_⟩
  · funext i
    change quadratic (Q₀.1 0) (T₀.carrierGradient Q₀ 0 (parameter ((u out).1, out.2))) i = _
    rw [hparam]
  · apply hweight F hF hi hrank hM (hclose.trans_le (min_le_right _ _))
      (hlow ⟨R.sourceChart j, a⟩) row col Φ Y initial _ _ r a₀ hηb hr ha har hcarrier
      b cJ V L G hf hInv htrans hgap hcJ out hout hk hmask'
    · rw [hparam]
      exact hmin row col hzW
    · rw [hparam]
      exact hi₀

end JanetCartan.ContinuumNormal.FrozenModel
