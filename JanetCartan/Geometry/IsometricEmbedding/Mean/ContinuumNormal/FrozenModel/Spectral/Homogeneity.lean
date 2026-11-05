module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.CanonicalData
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.JacobianRegularity
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.HighFrequency

/-!
# Exact high-frequency homogeneity of the frozen carrier symbols

The sphere compactness step of `app:ch_background:prop:bg-frame` uses the
literal canonical reflected symbol. The input norm cancels the actual
degree-one Jacobian, and the original high cutoff is one above the geometric
output threshold. No angular mask, inverse, support, or measure is changed.
The local geometric inputs are produced by `exists_frozen_conic_inputs`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic
open ContinuumNormalReduction TransportSymbol ConicChart

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a b cJ : ℝ}
    {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    {c C : ℝ} (hP : P.IsValid c C)
    (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a) (har : 6 * a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)))
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ (6 * a),
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)

local notation "J₀" => transportAbsoluteJacobian (adaptedSliceCoordinates T)
  (normalizedTransportPosition T Q 0)
local notation "u₀" => frozenSymbolInverse T Q z₀ ηb r (6 * a)
local notation "Ω₀" => frozenSymbolDomain T Q z₀ ηb r (6 * a)

include hP hηb hr har hcarrier hf hInv htrans

/-- Degree-one scaling of the literal zero-scale Jacobian, on the original
input cone. This supplies the cancellation used in the frozen spectral gap
(`app:ch_background:eq:bg-jacobian`). -/
theorem frozenJacobian_scaling {p : InputVariables n}
    (hp : p ∈ frozenInputDomain z₀ ηb r (6 * a)) {t : ℝ} (ht : 0 < t) :
    J₀ (scaleInput t p) = t * J₀ p := by
  have htp : scaleInput t p ∈ frozenInputDomain z₀ ηb r (6 * a) :=
    ⟨hp.1, radialScale_mem_supportedCone hp.2 ht⟩
  rw [frozenJacobian_eq_origin T Q hP hr har hcarrier (adaptedSliceCoordinates T) htp,
    frozenJacobian_eq_origin T Q hP hr har hcarrier (adaptedSliceCoordinates T) hp]
  exact transportAbsoluteJacobian_scaling T Q hηb hr hf hInv htrans hp ht

variable (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)

local notation "angular₀" => angularMask z₀ (NormedSpace.normalize ηb) ha
  (And.left (angularWidth_spec hηb hr))
local notation "a₀" => uncutFrozenCoefficients T Q F row col Φ Y initial
  angular₀ FixedCutoffs.highFrequency
local notation "S₀" => closedBall (spectatorCenter z₀) (a / 2)

/-- Exact homogeneity of the spectator integral with only its high mask
removed. The original Jacobian and inverse scaling are proved from the
retained chart (`app:ch_background:prop:bg-frame`, frozen limit). -/
theorem frozenHomogeneousAmplitude_smul {t : ℝ} (ht : 0 < t) (p : Variables n) :
    amplitude (homogeneousCoefficients a₀) J₀ u₀ Ω₀ S₀ (scaleFrequency t p) =
      amplitude (homogeneousCoefficients a₀) J₀ u₀ Ω₀ S₀ p := by
  apply amplitude_homogeneous _ _ _ _ _ ht
  · exact frozenSymbolDomain_smul_iff T Q z₀ ηb r (6 * a) ht
  · intro q hq
    exact frozenSymbolInverse_smul T Q hηb hr hInv htrans hq ht
  · intro q hq
    exact frozenJacobian_scaling T Q hP hηb hr har hcarrier hf hInv htrans
      (frozenSymbolInverse_maps T Q hηb hr hInv htrans hq) ht

variable (hgap : ∀ p ∈ physicalParameterSet z₀ (6 * a), ∀ u ∈ dataBox z₀ ηb (2 * r),
    ‖(G.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp
      (fderiv ℝ (adaptedTransportChart T Q p) u) -
        ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2)
include hgap

omit hP har hcarrier in
/-- Above the actual output-frequency threshold, the original high mask
can be removed from the literal density, including outside the inverse
domain (`app:ch_background:prop:bg-frame`, frozen limit). -/
theorem frozenExtendedDensity_eq_homogeneous_of_highFrequency
    (p : Variables n × Euclidean 2) (hk : frozenHighFrequencyRadius T G ≤ ‖p.1.2.2‖) :
    extendedDensity a₀ J₀ u₀ Ω₀ p =
      extendedDensity (homogeneousCoefficients a₀) J₀ u₀ Ω₀ p := by
  by_cases hp : p ∈ Ω₀
  · rw [extendedDensity, indicator_of_mem hp, extendedDensity, indicator_of_mem hp]
    apply inputDensity_eq_homogeneous_of_high_eq_one
    exact frozenInverse_highFrequency_one T G Q hηb hr hf hInv htrans hgap hp hk
  · simp only [extendedDensity, indicator_of_notMem hp]

omit hP har hcarrier in
/-- The high-cutoff spectator integral equals its homogeneous formula
above the geometric threshold, over the SAME Lebesgue spectator ball
(`app:ch_background:prop:bg-frame`, frozen limit). -/
theorem frozenAmplitude_eq_homogeneous_of_highFrequency
    (p : Variables n) (hk : frozenHighFrequencyRadius T G ≤ ‖p.2.2‖) :
    amplitude a₀ J₀ u₀ Ω₀ S₀ p = amplitude (homogeneousCoefficients a₀) J₀ u₀ Ω₀ S₀ p := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v ↦
    frozenExtendedDensity_eq_homogeneous_of_highFrequency T Q hηb hr ha hf hInv htrans
      F row col Φ Y initial hgap (p, v) hk

/-- Exact degree-zero scaling of the ACTUAL canonical reflected carrier
symbol whenever both frequencies exceed its geometric threshold. Both
reflections and the factor `2*(2π)^n` are retained. Initial multipliers are
unchanged and need no extra hypothesis for this identity
(`app:ch_background:prop:bg-frame`, frozen limit). -/
theorem canonicalFrozenCarrierSymbol_highFrequency_smul
    {t : ℝ} (ht : 0 < t) {k : Euclidean n}
    (hk : frozenHighFrequencyRadius T G ≤ ‖k‖)
    (htk : frozenHighFrequencyRadius T G ≤ ‖t • k‖) :
    canonicalFrozenCarrierSymbol T Q F row col Φ Y initial z₀ hηb hr ha (t • k) =
      canonicalFrozenCarrierSymbol T Q F row col Φ Y initial z₀ hηb hr ha k := by
  have he (l : Euclidean n) (hl : frozenHighFrequencyRadius T G ≤ ‖l‖)
      (htl : frozenHighFrequencyRadius T G ≤ ‖t • l‖) :
      amplitude a₀ J₀ u₀ Ω₀ S₀ (0, 0, t • l) = amplitude a₀ J₀ u₀ Ω₀ S₀ (0, 0, l) := by
    rw [frozenAmplitude_eq_homogeneous_of_highFrequency T Q hηb hr ha hf hInv htrans
      F row col Φ Y initial hgap (0, 0, t • l) htl,
      frozenAmplitude_eq_homogeneous_of_highFrequency T Q hηb hr ha hf hInv htrans
        F row col Φ Y initial hgap (0, 0, l) hl]
    exact frozenHomogeneousAmplitude_smul T Q hP hηb hr ha har hcarrier hf hInv htrans
      F row col Φ Y initial ht (0, 0, l)
  change (2 * (2 * Real.pi) ^ n) •
    (amplitude a₀ J₀ u₀ Ω₀ S₀ (0, 0, t • k) + amplitude a₀ J₀ u₀ Ω₀ S₀ (0, 0, -(t • k))) = _
  rw [he k hk htk, ← smul_neg t k,
    he (-k) (by simpa using hk) (by simpa using htk)]
  rfl

end JanetCartan.ContinuumNormal.FrozenModel
