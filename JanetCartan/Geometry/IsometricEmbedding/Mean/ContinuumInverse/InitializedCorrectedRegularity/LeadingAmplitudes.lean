module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.InitializedCorrectedRegularity.HighAmplitudes
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.RetainedLowBudget.OnGeometry
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.RetainedLowBudget.FullNormalFromNull

/-!
# High and sharp low amplitudes from the same retained leading wave

The original reserve-thirteen null estimate supplies the sharp full-normal
baseline. Its reserve-fourteen full-normal estimate supplies all high orders.
Both apply to the same supplied conic charts and masks. The current-history
constructor supplies these two estimates on its original working set and
compact leading ball; no amplitude or low normal estimate is assumed.

Consumer: the two carrier-profile inputs of
`exists_prescribed_history_elliptic_estimates_with_exterior` on the common row.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumInverse
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open NullTransport ActualFlow FlowAmplitude LeadingWave.FullModulation ProjectedStressFrame
open ContinuumRow LeadingPrimitive CanonicalCarrier CanonicalConic TransportKernel CarrierNormalRealization
open ContinuumNormalReduction.TransportSymbol ContinuumNormal.RetainedFrozen
open Pseudodifferential AmplitudeBound ContinuumCommutator.RetainedLowBudget

/-- The two estimates of the original full-leading construction give both
carrier hypotheses of the elliptic bootstrap, on the supplied masks. The sharp
baseline uses only the original fixed order `2*(n+1)+14`; each high estimate has
one map/scalar norm at order `s+14`. The source of the scalar and null estimates
is the actual retained history's `hsolution` continuation
(`app:ch_waves:eq:joint-tame`, `app:ch_background:eq:bg-commutator`). -/
theorem exists_reflected_high_and_baseline_of_retained_leading {n N : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (D : CoefficientNormCharts n)
    (Kinitial : Set (Euclidean (n - 1) × Euclidean 3))
    {Jfull : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hJfull : IsCompact Jfull) (hgraph : MapsTo (carrierGraph T) D.field.carrier Jfull)
    (zFull : Euclidean 3 × Euclidean (n - 1)) {σfull : ℝ} (hσfull : 0 < σfull)
    (hJfullEq : Jfull = closedBall ((0 : Euclidean n), zFull) σfull)
    (hJphysical : closedBall (0 : Euclidean n) (2 * σfull) ⊆ K)
    (hJphase : closedBall ((0 : Euclidean n), zFull) (2 * σfull) ⊆ domain T)
    (Wfull : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1))))
    (hWfull : IsCompact Wfull) (hJfullW : Jfull ⊆ Wfull)
    (E : Set (Euclidean n × CarrierParameter)) (hDE : D.field.region ⊆ E)
    (hfield : E ⊆ (U ∩ ball (0 : Euclidean n) T.physicalRadius) ×ˢ
      (parameter ⁻¹' parameterInterior (2 * P.radius)))
    (hphase : E ⊆ ball (0 : Euclidean n) T.family.radius ×ˢ
      (parameter ⁻¹' parameterInterior (3 * P.radius / 2)))
    (adet : Euclidean n × Euclidean 3) {ρdet : ℝ} (hρdet : 0 < ρdet)
    (hxdet : MapsTo Prod.fst (closedBall adet ρdet)
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius))
    (hdet : closedBall adet ρdet ⊆
      ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius))
    (hmaps : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2))
      D.field.carrier (closedBall adet ρdet))
    (z₀ : Euclidean 3) {ηb : Euclidean (n - 1)} (hηb : ηb ≠ 0)
    {r a r' a' : ℝ} (hr : 0 < r) (hr' : 0 < r') (ha' : 0 < a')
    (hcell : 4 * a' < 1 / 2) (houter : coefficientDomain z₀ r (6 * a) ⊆ E)
    (hsupport : tsupport (FixedCutoffs.physical (n := n) ha' 1) ×ˢ
      carrierSupport z₀ (r := a') ⊆ D.field.carrier)
    (p₀ : InputVariables n) (q₀ : Variables n × Euclidean 2)
    {ρ τ : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ)
    {W Bi : Set (InputVariables n)} (hW : IsOpen W)
    (hKiW : closedBall p₀ ρ ⊆ W) (hBi : IsCompact Bi) (hWBi : W ⊆ Bi)
    (hBiDom : Bi ⊆ symbolInputDomain z₀ ηb r (6 * a))
    (hfoot : ∀ p ∈ closedBall p₀ ρ, D.Contains p)
    {It : Set ℝ} (hIt : IsOpen It) (hIIt : Icc (0 : ℝ) 1 ⊆ It)
    (hsegT : ∀ t ∈ It, MapsTo (transportSegmentInput n t) W D.field.region)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W D.field.carrier)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {ε gap δgeometry : ℝ} (hε : 0 < ε) (hgap : 0 < gap) (hδgeometry : 0 < δgeometry)
    (hfreq : ∀ p ∈ Bi, ε ≤ ‖p.2.2‖)
    (hgeometry : ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
      (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < δgeometry →
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      RetainedSpectralGeometry T Q z₀ ηb r a ∧
      closedBall q₀ (2 * τ) ⊆ symbolDomain T Q z₀ ηb r (6 * a) ∧
      MapsTo (inverseCoordinates (symbolInverse T Q z₀ ηb r (6 * a)))
        (closedBall q₀ (2 * τ)) (closedBall p₀ ρ) ∧
      (∀ p ∈ closedBall p₀ ρ, ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ Bi, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (transportPosition T Q) p) ∧
      (closure (augmentedTransportGradient (transportPosition T Q) ''
        conicMaskSupport z₀ ηb r' a') ∩ {p | p.1.2.2 ≠ 0} ⊆
          symbolDomain T Q z₀ ηb r (6 * a)) ∧
      (∀ x : Variables n, ‖x.2.2‖ = 1 / 4 → ∀ v : Euclidean 2,
        (x, v) ∈ closure (augmentedTransportGradient (transportPosition T Q) ''
          conicMaskSupport z₀ ηb r' a') → (x, v) ∈ closedBall q₀ τ) ∧
      (∀ p ∈ symbolDomain T Q z₀ ηb r (6 * a),
        ‖(symbolInverse T Q z₀ ηb r (6 * a) p).2‖ ≤ 2 * ‖p.1.2.2‖)) :
    ∃ δ > (0 : ℝ),
    ∀ (Bfull : ℕ → ℝ), (∀ j, 0 < Bfull j) →
    ∀ (Bnull : ℕ → ℝ) {MF Minitial κmet κ : ℝ},
      0 ≤ MF → 0 ≤ Minitial → 0 < κmet → 0 < κ →
    ∃ Cbaseline > (0 : ℝ), ∃ Cprofile : ℕ → ℝ, (∀ s, 0 < Cprofile s) ∧
    ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
      (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      cNorm K (2 * (n + 1) + 14) F ≤ MF →
      (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < δ →
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      ∀ (row col : Fin n)
        (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
          Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
        (φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
        (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
        (O : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1))))
        (Vcomp : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))),
      IsOpen O → MapsTo Prod.fst O U → O ⊆ domain T →
      closedBall ((0 : Euclidean n), zFull) (2 * σfull) ⊆ O → Wfull ⊆ O →
      MapsTo (carrierGraph T) E O →
      MapsTo (fun p : Euclidean n × CarrierParameter ↦
        coordinates (adaptedCoordinates T.data.adapted) (p.1, parameter p.2)) E Vcomp →
      ContDiffOn ℝ ∞ (fun w ↦ scalarAmplitude T Q F row col Φ Y initial w •
        nullvector T Q col w) O →
      (∀ q ∈ Vcomp, let w := (coordinates (adaptedCoordinates T.data.adapted)).symm q
        scalarAmplitude T Q F row col Φ Y initial
          (w.1, (w.2, T.reference.spatialPatch w.2)) =
            carrierScalarAmplitude T Q F row col φ y initial w) →
      cNorm Kinitial (2 * (n + 1) + 14) initial ≤ Minitial →
      (∀ j, cNorm Wfull j
          (fun w ↦ scalarAmplitude T Q F row col Φ Y initial w • nullvector T Q col w) ≤
        Bnull j * (1 + cNorm K (j + 13) F + cNorm Kinitial (j + 13) initial)) →
      (∀ j, cNorm Jfull j (fullNormal T Q F row col Φ Y initial) ≤
        Bfull j * (1 + cNorm K (j + 14) F + cNorm Kinitial (j + 14) initial)) →
      let e := data T Q F row col φ y initial ha' hcell
        (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
        FixedCutoffs.highFrequency
      let d := coefficientsOfCarrier e (FixedCutoffs.physical ha' 1)
      let b := fullReflectedMatrixAmplitude d (symbolJacobian T Q)
        (symbolInverse T Q z₀ ηb r (6 * a)) (symbolDomain T Q z₀ ηb r (6 * a))
        (closedBall (spectatorCenter z₀) (a' / 2))
      ContDiff ℝ ∞ (Function.uncurry b) ∧
      (∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j)
        (2 * (n + 1) + 1) Cbaseline) ∧
      ∀ s : ℕ, 2 ≤ s → ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j)
        s (Cprofile s * (1 + cNorm K (s + 14) F + cNorm Kinitial (s + 14) initial)) := by
  obtain ⟨δhigh, hδhigh, hhigh⟩ :=
    exists_reflected_profiles_on_initialized_density_geometry T (N := N) hP hK hKU hball
      D Kinitial hJfull hgraph E hDE hfield hphase adet hρdet hxdet hdet hmaps
      z₀ hηb hr hr' ha' hcell houter hsupport p₀ q₀ hρ hτ hW hKiW hBi hWBi
      hBiDom hfoot hIt hIIt hsegT hseg A hε hgap hδgeometry hfreq hgeometry
  obtain ⟨δbase, hδbase, hbaseline⟩ :=
    exists_reflected_baseline_on_retained_geometry T (N := N) hP hK hKU hball
      D hJfull hgraph E hDE hfield hphase adet hρdet hxdet hdet hmaps
      z₀ hηb hr hr' ha' hcell houter p₀ q₀ hρ hτ hW hKiW hBi hWBi
      hBiDom hfoot hIt hIIt hsegT hseg A hε hgap hδgeometry hfreq hgeometry
  refine ⟨min δhigh δbase, lt_min hδhigh hδbase, ?_⟩
  intro Bfull hBfull Bnull MF Minitial κmet κ hMF hMinitial hκmet hκ
  obtain ⟨Bnormal, hBnormal, hnormalLow⟩ := exists_fullNormal_low_bound_of_null_bounds T (N := N)
    hK hKU hball zFull hσfull hJphysical hJphase Kinitial Bnull hMF hMinitial hκmet hκ
  obtain ⟨Cbaseline, hCbaseline, hbaseline⟩ := hbaseline hMF hBnormal.le hκmet hκ
  choose Cprofile hCprofile hhigh using fun s : ℕ ↦
    hhigh Bfull hBfull hMF hMinitial hκmet hκ (max s 2) (le_max_right _ _)
  refine ⟨Cbaseline, hCbaseline, Cprofile, hCprofile, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hlow hclose Q row col Φ Y φ y initial O Vcomp
    hO hOU hOphase hJ₂O hWO hgraphO hcompE hnull hcomp hinitial hnullBound hfull
  have hJO : Jfull ⊆ O := by
    rw [hJfullEq]
    exact (closedBall_subset_closedBall (by linarith)).trans hJ₂O
  have hnullJ (j : ℕ) : cNorm (closedBall ((0 : Euclidean n), zFull) σfull) j
        (fun w ↦ scalarAmplitude T Q F row col Φ Y initial w • nullvector T Q col w) ≤
      Bnull j * (1 + cNorm K (j + 13) F + cNorm Kinitial (j + 13) initial) := by
    rw [← hJfullEq]
    exact (cNorm_mono_set_of_contDiffAt hJfullW hWfull
      (fun w hw ↦ (hnull.contDiffAt (hO.mem_nhds (hWO hw))).of_le (by simp))).trans
        (hnullBound j)
  have hfullLow : cNorm Jfull (2 * (n + 1) + 1)
      (fullNormal T Q F row col Φ Y initial) ≤ Bnormal := by
    rw [hJfullEq]
    exact hnormalLow Q F row col Φ Y initial O rfl hF hi hrank hFM hinitial
      hmet hnormal hJ₂O hnull hnullJ
  have hbase := hbaseline F hF hi hrank hFM hmet hnormal hlow
    (hclose.trans_le (min_le_right _ _)) row col Φ Y φ y initial O Vcomp
    hO hOU hOphase hJO hgraphO hcompE hnull hcomp hfullLow
  refine ⟨hbase.1, hbase.2, ?_⟩
  intro s hs
  have hh := hhigh s F hF hi hrank ((cNorm_mono_order (by omega)).trans hFM)
    hmet hnormal hlow (hclose.trans_le (min_le_left _ _)) row col Φ Y φ y initial O Vcomp
    hO hOU hOphase hJO hgraphO hcompE hnull hcomp
    ((cNorm_mono_order (by omega)).trans hinitial) hfull
  simpa only [max_eq_left hs] using hh.2

end JanetCartan.ContinuumInverse
