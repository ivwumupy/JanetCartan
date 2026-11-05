module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Coordinates
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FrequencyCutoffs

/-!
# The geometric high-frequency threshold

The high mask in `app:ch_background:prop:bg-frame` is applied to the inverse
input covector, not to the physical output frequency. A fixed differential
bound for the retained reference chart gives the actual comparison constant.
The resulting threshold is chosen using that reference chart and its fixed
orthogonal coordinates, independently of the immersion and current frame.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open ContinuumNormalReduction TransportSymbol ConicChart

/-- The fixed reference half-gap bounds all current slice differentials.
This is the numerical input to `frozenFrequencyBound` (`bg-jacobian`). -/
def frozenReferenceDifferentialBound {n : ℕ}
    (G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))) : ℝ :=
  (exists_reference_differential_upper G).choose

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1)))

/-- A fixed physical frequency comparison bound from the SAME reference
chart and volume-preserving coordinates (`app:ch_background:eq:bg-Psi`). -/
def frozenFrequencyBound : ℝ :=
  (1 + ‖(adaptedSliceCoordinates T).equiv.symm.toContinuousLinearMap‖) * frozenReferenceDifferentialBound G

/-- The geometric frequency comparison constant is strictly positive
(`app:ch_background:prop:bg-frame`, frozen step). -/
theorem frozenFrequencyBound_pos : 0 < frozenFrequencyBound T G :=
  mul_pos (by positivity) (exists_reference_differential_upper G).choose_spec.1

/-- The actual high-frequency threshold includes the inverse frequency
comparison, as required in the frozen step of `app:ch_background:prop:bg-frame`.
It also ensures the image factor `|k|²/(1+|k|²)` is at least one half. -/
def frozenHighFrequencyRadius : ℝ := max 1 (2 * frozenFrequencyBound T G)

/-- The geometric threshold is at least one (`app:ch_background:prop:bg-frame`). -/
theorem one_le_frozenHighFrequencyRadius : 1 ≤ frozenHighFrequencyRadius T G := le_max_left _ _

variable
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a b cJ : ℝ}
    {V L : Set (ℝ × Euclidean (n - 1))}
    (hηb : ηb ≠ 0) (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ a ×ˢ dataSet z₀ ηb (3 * r)))
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ a)
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ a,
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)
    (hgap : ∀ p ∈ physicalParameterSet z₀ a, ∀ u ∈ dataBox z₀ ηb (2 * r),
      ‖(G.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp
        (fderiv ℝ (adaptedTransportChart T Q p) u) -
          ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2)
include hηb hr hf hInv htrans hgap

/-- The retained frozen inverse satisfies the actual physical comparison.
The bound depends only on the reference chart; all current-frame hypotheses
are outputs of the existing canonical local-chart producers (`bg-Psi`). -/
theorem frozenInverse_frequency_comparison {p : Variables n × Euclidean 2}
    (hp : p ∈ frozenSymbolDomain T Q z₀ ηb r a) :
    ‖p.1.2.2‖ ≤ frozenFrequencyBound T G * ‖(frozenSymbolInverse T Q z₀ ηb r a p).2‖ := by
  have hm := symbolInverse_maps T Q hηb hr hInv htrans hp
  have hD : ∀ D : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1)),
      ‖(G.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp D -
        ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2 → ‖D‖ ≤ frozenReferenceDifferentialBound G :=
    fun D hD ↦ ((exists_reference_differential_upper G).choose_spec.2 D hD).1
  have hb := (adaptedTransportChart_norm_bounds T Q hηb hr hf hInv htrans hgap hD hm.1 hm.2).2
  have hc := physicalTransportChart_norm_le_adapted T Q (p.2, 0, 0)
    (frozenSymbolInverse T Q z₀ ηb r a p)
  have he := transportAveragedGradient_symbolInverse T Q hηb hr hInv htrans hp
  change transportAveragedGradient (transportPosition T Q)
    ((0, 0), ((frozenSymbolInverse T Q z₀ ηb r a p).1, p.2),
      (frozenSymbolInverse T Q z₀ ηb r a p).2) = p.1.2.2 at he
  rw [he] at hc
  have hb' := mul_le_mul_of_nonneg_left hb
    (norm_nonneg (adaptedSliceCoordinates T).equiv.symm.toContinuousLinearMap)
  apply hc.trans (hb'.trans _)
  change ‖(adaptedSliceCoordinates T).equiv.symm.toContinuousLinearMap‖ *
      (frozenReferenceDifferentialBound G * ‖(frozenSymbolInverse T Q z₀ ηb r a p).2‖) ≤
    (1 + ‖(adaptedSliceCoordinates T).equiv.symm.toContinuousLinearMap‖) *
      frozenReferenceDifferentialBound G * ‖(frozenSymbolInverse T Q z₀ ηb r a p).2‖
  have hn : 0 ≤ frozenReferenceDifferentialBound G * ‖(frozenSymbolInverse T Q z₀ ηb r a p).2‖ :=
    mul_nonneg (exists_reference_differential_upper G).choose_spec.1.le (norm_nonneg _)
  nlinarith

/-- At the proved output threshold the ORIGINAL input high mask is one.
There is no replacement of the geometric threshold by `2`
(`app:ch_background:prop:bg-frame`, frozen step). -/
theorem frozenInverse_highFrequency_one {p : Variables n × Euclidean 2}
    (hp : p ∈ frozenSymbolDomain T Q z₀ ηb r a)
    (hk : frozenHighFrequencyRadius T G ≤ ‖p.1.2.2‖) :
    FixedCutoffs.highFrequency ‖(frozenSymbolInverse T Q z₀ ηb r a p).2‖ = 1 := by
  apply FixedCutoffs.highFrequency_one
  have hb := frozenInverse_frequency_comparison T G Q hηb hr hf hInv htrans hgap hp
  have hlarge : 2 * frozenFrequencyBound T G ≤ ‖p.1.2.2‖ :=
    (le_max_right _ _).trans hk
  have hC := frozenFrequencyBound_pos T G
  nlinarith

end JanetCartan.ContinuumNormal.FrozenModel
