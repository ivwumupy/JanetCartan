module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Construction
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Incidence.Normal

/-!
# Strict positivity of the literal canonical frozen weight

For `app:ch_background:prop:bg-frame`, this leaf combines the primitive normal
producer with the actual conic inverse, its positive Jacobian and its geometric
high-frequency threshold. The remaining incidence geometry must place each
selected root in the inverse domain and the original mask plateau. No positive
weight or nonzero normal is a construction hypothesis.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic
open ContinuumNormalReduction TransportSymbol ConicChart
open NullTransport ProjectedStressFrame

/-- A primitive frame threshold makes the literal canonical input weight
strictly positive at every plateau inverse point above the GEOMETRIC output
frequency threshold. The inverse, Jacobian and original masks are exactly
those of `canonicalFrozenCarrierSymbol` (`app:ch_background:prop:bg-frame`).

Producers: `exists_frozen_unit_normal_gap` constructs the normal gap from
immersion/rank/frame/minor data; `exists_frozen_conic_inputs` constructs `hf`,
`hInv`, `htrans`, `hgap` and `hcJ`; `exists_actual_null_gaps` supplies the
selected minor. Incidence geometry must still instantiate `hp` and `hmask`
at the SAME roots of `exists_constructed_incidence_detection`. The allowed
initial multiplier is retained at its actual transport footpoint.
-/
theorem exists_canonicalFrozen_weight_threshold {n : ℕ} (hn : 5 ≤ n)
    {P : Patch n} {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (M : ℝ) {μ : ℝ} (hμ : 0 < μ) :
    ∃ δ > (0 : ℝ),
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n))
        (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
        (hrank : HasFullNormalRankOn F U),
        cNorm K 4 F ≤ M →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < δ →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ∀ (row col : Fin n)
          (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
          (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
          (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r a : ℝ)
          (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a),
          6 * a ≤ 3 * r →
          (closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
            carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) →
          ∀ (b cJ : ℝ) (V L : Set (ℝ × Euclidean (n - 1)))
            (G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))),
          ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
            (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)) →
          BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
            (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G →
          (∀ p ∈ physicalParameterSet z₀ (6 * a),
            ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
              ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖) →
          (∀ p ∈ physicalParameterSet z₀ (6 * a), ∀ u ∈ dataBox z₀ ηb (2 * r),
            ‖(G.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp
              (fderiv ℝ (adaptedTransportChart T Q p) u) -
                ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2) →
          0 < cJ →
          let u := frozenSymbolInverse T Q z₀ ηb r (6 * a)
          let angular := angularMask z₀ (NormedSpace.normalize ηb) ha (angularWidth_spec hηb hr).1
          ∀ p ∈ frozenSymbolDomain T Q z₀ ηb r (6 * a),
            frozenHighFrequencyRadius T G ≤ ‖p.1.2.2‖ →
            angular ((u p).1, p.2) (‖(u p).2‖⁻¹ • (u p).2) = 1 →
            μ ≤ |(reducedSymbol (Q.1 0)
              (T.carrierGradient Q 0 (parameter ((u p).1, p.2)))).adjugate row col| →
            1 / 2 ≤ initial (Y (0, (0, parameter ((u p).1, p.2)))) →
            0 < inputWeight (uncutFrozenCoefficients T Q F row col Φ Y initial
                angular FixedCutoffs.highFrequency)
              (transportAbsoluteJacobian (adaptedSliceCoordinates T)
                (normalizedTransportPosition T Q 0)) (inverseCoordinates u p) := by
  obtain ⟨δ, g, hδ, hg, hnormal⟩ := exists_frozen_unit_normal_gap hn hP T hK hKU hball M hμ
  refine ⟨δ, hδ, ?_⟩
  intro F hF hi hrank hM hclose hlow Q row col Φ Y initial z₀ ηb r a hηb hr ha
    har hcarrier b cJ V L G hf hInv htrans hgap hcJ u angular p hp hk hmask hminor hi₀
  have hpin := frozenSymbolInverse_maps T Q hηb hr hInv htrans hp
  have hz := carrierInterior_of_frozenInputDomain hr har hcarrier hpin
  have hn := hnormal F hF hi hrank hM hclose hlow row col Φ Y ((u p).1, p.2)
    (fun i ↦ (hz i).le) hminor
  have hnpos : 0 < ‖normalField T Q F row col Φ Y (fun _ ↦ 1) 0 ((u p).1, p.2)‖ :=
    hg.trans_le hn
  have hJ := frozenJacobian_pos T Q hP hηb hr har hcarrier hInv htrans hf hcJ hpin
  have hhigh := frozenInverse_highFrequency_one T G Q hηb hr hf hInv htrans hgap hp hk
  have hη : 0 < ‖(u p).2‖ := norm_pos_iff.mpr hpin.2.2.1
  have hw : 0 < inputWeight (uncutFrozenCoefficients T Q F row col Φ Y (fun _ ↦ 1)
      angular FixedCutoffs.highFrequency)
      (transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (normalizedTransportPosition T Q 0)) (inverseCoordinates u p) := by
    change 0 < 1 * 1 * angular ((u p).1, p.2) (‖(u p).2‖⁻¹ • (u p).2) ^ 2 *
      FixedCutoffs.highFrequency ‖(u p).2‖ ^ 2 * ‖(u p).2‖ /
        transportAbsoluteJacobian (adaptedSliceCoordinates T)
          (normalizedTransportPosition T Q 0) (inverseCoordinates u p) *
      ‖normalField T Q F row col Φ Y (fun _ ↦ 1) 0 ((u p).1, p.2)‖ ^ 2 *
      ‖normalField T Q F row col Φ Y (fun _ ↦ 1) 0 ((u p).1, p.2)‖ ^ 2
    rw [hmask, hhigh]
    positivity
  have hmult := frozenInputWeight_multiplier_lower_bound T Q F row col Φ Y initial
    angular FixedCutoffs.highFrequency
    (transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Q 0))
    (inverseCoordinates u p) hJ.le hi₀
  exact (mul_pos (by norm_num) hw).trans_le hmult

end JanetCartan.ContinuumNormal.FrozenModel
