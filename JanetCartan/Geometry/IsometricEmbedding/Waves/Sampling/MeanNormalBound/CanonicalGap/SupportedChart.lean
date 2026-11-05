module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.CanonicalGap.PhaseIdentification
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualInverses

/-!
# The actual supported full-phase frequency gap

The annulus is produced by `exists_actual_buffered_inverses_with_caps` for
the actual current phase and transferred through the SAME physical and input
coordinates. The inverse and its compact core are retained for the parent
`UniformNormalData` construction. No inverse-amplitude support gap is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.MeanNormalBound.CanonicalGap
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison NormalComparison
open ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Compact normalized input support in the existing measure-preserving
coordinates, including incidence and the entire covector box
(`app:ch_seed:prop:seed-phase-charts`). -/
def normalizedInputCore (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r : ℝ) :
    Set (Euclidean n) :=
  (adaptedSliceCoordinates T).equiv ⁻¹' dataBox z₀ ηb r

/-- The original input core is compact, before the current data or labels
are chosen (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem normalizedInputCore_compact (z₀ : Euclidean 3)
    (ηb : Euclidean (n - 1)) (r : ℝ) : IsCompact (normalizedInputCore T z₀ ηb r) :=
  (adaptedSliceCoordinates T).equiv.toHomeomorph.isCompact_preimage.mpr
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))

/-- The compact core retains the open radius-two data buffer
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem normalizedInputCore_subset_chart (z₀ : Euclidean 3)
    (ηb : Euclidean (n - 1)) {r : ℝ} (hr : 0 < r) :
    normalizedInputCore T z₀ ηb r ⊆
      (adaptedSliceCoordinates T).equiv ⁻¹' dataSet z₀ ηb (2 * r) :=
  fun _ hu ↦ (dataBox_geometry z₀ ηb hr).2.2.2 hu

/-- The actual annular gap, chosen before current data, epsilon, radial bands
and spectators. The full buffered inverse is retained on the SAME charts.
The bound holds on the outer data box, so every smaller compact angular/input
support is allowed. This supplies the canonical producer of the primitive gap
in `FrequencySupport.pairedInverseAmplitude_frequency_lower`
(`app:ch_seed:eq:seed-normal-annulus`). -/
theorem exists_buffered_normalizedFullPhase_gap {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {rmax emax : ℝ} (hrmax : 0 < rmax) (hemax : 0 < emax) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    let R := FrozenIncidence.referenceEquiv T hP hz₀ hinc hd
    ∃ r > (0 : ℝ), r ≤ rmax ∧ ∃ s > (0 : ℝ), s ≤ r ∧
      3 * r < T.family.radius / 8 ∧
      (closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
        carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) ∧
    ∃ e > (0 : ℝ), e ≤ emax ∧ ∃ δ > (0 : ℝ), ∃ γ > (0 : ℝ),
    ∃ cF > (0 : ℝ), ∃ bF > (0 : ℝ), ∃ V L : Set (ℝ × Euclidean (n - 1)),
      IsOpen V ∧ IsCompact (closure V) ∧ IsCompact L ∧ L ⊆ V ∧
      ∀ Q,
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress n) < δ →
        BufferedPhaseInverse (fullChartFamily (current T Q) (spatialCarrier T))
          (fullParameterSet z₀ s (2 * e))
          (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r))
          V L bF cF R ∧
        ∀ ε ∈ Icc 0 e,
          ∀ v ∈ closedBall (spectatorCenter z₀) (s / 2),
          ∀ x ∈ closedBall 0 (s / 2), ∀ y ∈ closedBall 0 (s / 2),
          ∀ u ∈ normalizedInputCore T z₀ ηb (2 * r),
            γ ≤ ‖averagedGradient (normalizedFullPhase T Q v ε) x y u‖ := by
  obtain ⟨r, hr, hrmax', s, hs, hsr, hphys, hcarrier, e, he, hemax', δ, hδ,
    cF, hcF, bF, hbF, V, L, cT, _, bT, _, VT, LT, γ, hγ, B, _,
    hV, hVc, hLc, hLV, _, _, _, _, hall⟩ :=
      ActualInverses.exists_actual_buffered_inverses_with_caps T hP hz₀ hk hinc hd
        hrmax hemax
  refine ⟨r, hr, hrmax', s, hs, hsr, hphys, hcarrier, e, he, hemax', δ, hδ,
    γ, hγ, cF, hcF, bF, hbF, V, L, hV, hVc, hLc, hLV, ?_⟩
  intro Q hQ
  obtain ⟨_, _, _, _, hinv, _, _, _, hann⟩ := hall Q hQ
  refine ⟨hinv, ?_⟩
  intro ε hε v hv x hx y hy u hu
  exact ((hann _ (fullPhaseParameters_mem T hs he hε hv hx hy) _ hu).2.1).trans
    (fullChart_norm_le_averagedGradient T Q v ε x y u)

end JanetCartan.Sampling.MeanNormalBound.CanonicalGap
