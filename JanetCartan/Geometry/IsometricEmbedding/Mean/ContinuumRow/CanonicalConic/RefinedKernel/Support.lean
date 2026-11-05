module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.RefinedSupport

/-!
# Refined masks inside the retained kernel chart

The original compact band uses the smaller mask radii; its forward image and
slice buffers stay in the outer conic chart. These deductions consume the radius
inequalities of `exists_actual_refined_supported_geometry` and supply
`refinedKernelSymbolInputs` for the supported carrier constructor.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualComparison CanonicalCarrier ContinuumNormalReduction TransportSymbol

variable {n : ℕ}

/-- Enlarging the carrier and angular radii enlarges the original open input
cone. Consumer: the smaller-mask kernel support (`app:ch_background:defn:bg-row`). -/
theorem symbolInputDomain_mono (z₀ : Euclidean 3) (ηb : Euclidean (n - 1))
    {r' r a' a : ℝ} (hrr : r' ≤ r) (haa : a' ≤ a) :
    symbolInputDomain z₀ ηb r' a' ⊆ symbolInputDomain z₀ ηb r a := by
  intro p hp
  exact ⟨⟨ball_subset_ball haa hp.1.1, ball_subset_ball haa hp.1.2.1,
    ball_subset_ball haa hp.1.2.2⟩,
    ball_subset_ball hrr hp.2.1, hp.2.2.1,
    ball_subset_ball (angularWidth_mono ηb hrr) hp.2.2.2⟩

/-- The smaller finite-band input support remains strictly inside the retained
outer cone (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem refined_bandInputSupport_subset {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)}
    {r' r a' a R : ℝ} (hηb : ηb ≠ 0) (hr' : 0 < r') (ha' : 0 < a')
    (hrr : r' ≤ r) (haa : a' ≤ a) (har' : a' ≤ r') :
    bandInputSupport z₀ ηb r' a' R ⊆ symbolInputDomain z₀ ηb r (6 * a) :=
  (bandInputSupport_subset hηb hr' ha' har').trans
    (symbolInputDomain_mono z₀ ηb hrr (mul_le_mul_of_nonneg_left haa (by norm_num)))

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r' r a' a R : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (hr' : 0 < r') (ha' : 0 < a')
    (hrr : r' ≤ r) (haa : a' ≤ a) (har' : a' ≤ r')

include hηb hr' ha' hrr haa har' in
/-- The actual forward image of the smaller finite band has the outer image
buffer required by `refinedKernelSymbolInputs` (`bg-full-complex-amplitude`). -/
theorem refined_bandImage_subset_symbolDomain :
    augmentedTransportGradient (transportPosition T Q) '' bandInputSupport z₀ ηb r' a' R ⊆
      symbolDomain T Q z₀ ηb r (6 * a) := by
  rintro _ ⟨p, hp, rfl⟩
  have hp' := refined_bandInputSupport_subset hηb hr' ha' hrr haa har' hp
  exact ⟨hp'.1, (p.2.1.1, p.2.2), hp'.2, rfl⟩

include hηb hr hr' ha' hrr haa har' in
/-- Compactness of the smaller finite-band image follows from smoothness on
the retained outer domain, without shrinking its inverse (`bg-Psi`). -/
theorem refined_bandImage_compact
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r))) :
    IsCompact (augmentedTransportGradient (transportPosition T Q) ''
      bandInputSupport z₀ ηb r' a' R) := by
  apply (bandInputSupport_compact z₀ ηb r' a' R).image_of_continuousOn
  have hh := (transportAveragedGradient_smooth_on_symbolInputDomain T Q hηb hr hf).continuousOn
  exact ((continuousOn_fst.fst.prodMk (continuousOn_fst.snd.prodMk hh)).prodMk
    continuousOn_snd.fst.snd).mono
      (refined_bandInputSupport_subset hηb hr' ha' hrr haa har')

include hηb hr hr' ha' hrr haa har' in
/-- Every spectator slice of the refined finite-band image is closed. Together
with its outer image buffer this justifies smooth zero extension of the
literal amplitude (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem refined_bandImage_slice_closed
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)))
    (p : Variables n) :
    IsClosed {v : Euclidean 2 | (p, v) ∈
      augmentedTransportGradient (transportPosition T Q) '' bandInputSupport z₀ ηb r' a' R} :=
  (refined_bandImage_compact T Q hηb hr hr' ha' hrr haa har' hf).isClosed.preimage
    (continuous_const.prodMk continuous_id)

end JanetCartan.ContinuumRow.CanonicalConic
