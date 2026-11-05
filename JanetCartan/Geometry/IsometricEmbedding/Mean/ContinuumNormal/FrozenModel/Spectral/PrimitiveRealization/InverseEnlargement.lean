module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.CanonicalData
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.RefinedKernel.Support

/-!
# Matching smaller frozen masks with an outer inverse

The supported-shell construction retains an outer inverse while shrinking the
original masks. These identities compare that expression with the canonical
frozen symbol using the smaller inverse. Both inverses must be constructed:
the hypotheses below are local conic inputs, not an assumed normal identity.
No mask, spectator measure, reflection or Fourier normalization is changed.

Consumer: the supported primitive realization and its Fourier identification
in `app:ch_background:prop:bg-frame`; source: `new:lem:scaling`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open ContinuumNormalReduction TransportSymbol

section Geometry

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a r' a' : ℝ}
    (hrr : r' ≤ r) (haa : a' ≤ a)

include hrr haa

omit T Q in
/-- Frozen input domains enlarge with the two radii. Only the original
incidence and spectator restrictions change (`app:ch_background:eq:bg-Psi`). -/
theorem frozenInputDomain_mono :
    frozenInputDomain z₀ ηb r' a' ⊆ frozenInputDomain z₀ ηb r a :=
  preimage_mono (symbolInputDomain_mono z₀ ηb hrr haa)

/-- The actual frozen images enlarge with the same two radii, independently
of the chosen inverse (`app:ch_background:eq:bg-Psi`). -/
theorem frozenSymbolDomain_mono :
    frozenSymbolDomain T Q z₀ ηb r' a' ⊆ frozenSymbolDomain T Q z₀ ηb r a := by
  rintro p ⟨hp, u, hu, he⟩
  refine ⟨⟨ball_subset_ball haa hp.1, ball_subset_ball haa hp.2.1,
    ball_subset_ball haa hp.2.2⟩, u, ?_, he⟩
  exact ⟨ball_subset_ball hrr hu.1, hu.2.1,
    ball_subset_ball (angularWidth_mono ηb hrr) hu.2.2⟩

variable {c C : ℝ} (hP : P.IsValid c C)
    (hηb : ηb ≠ 0) (hr : 0 < r) (hr' : 0 < r')
    (har : a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    {b cJ b' cJ' : ℝ} {V L V' L' : Set (ℝ × Euclidean (n - 1))}
    {G G' : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ a)
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ a,
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)
    (hInv' : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ a')
      (dataBox z₀ ηb r') (dataSet z₀ ηb (2 * r')) (dataBox z₀ ηb (2 * r')) V' L' b' cJ' G')
    (htrans' : ∀ p ∈ physicalParameterSet z₀ a',
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r' (angularWidth ηb r'),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r' / 4) * ‖u.2‖)

include hrr haa hP hηb hr hr' har hcarrier hInv htrans hInv' htrans'

/-- The retained outer inverse agrees with the smaller canonical inverse
where the latter is defined. This is proved by the actual left-inverse
identity, so shrinking masks never silently changes the inverse used by
the canonical frozen symbol (`app:ch_background:eq:bg-Psi`). -/
theorem frozenSymbolInverse_eq_of_enlargement
    {p : Variables n × Euclidean 2} (hp : p ∈ frozenSymbolDomain T Q z₀ ηb r' a') :
    frozenSymbolInverse T Q z₀ ηb r a p = frozenSymbolInverse T Q z₀ ηb r' a' p := by
  have hsmall := frozenSymbolInverse_maps T Q hηb hr' hInv' htrans' hp
  have hlarge := frozenInputDomain_mono hrr haa hsmall
  have hleft := frozenInverse_augmentedGradient T Q hP hηb hr har hcarrier hInv htrans hlarge
  have hright : augmentedTransportGradient (normalizedTransportPosition T Q 0)
      (inverseCoordinates (frozenSymbolInverse T Q z₀ ηb r' a') p) = p := by
    apply augmentedTransportGradient_inverseCoordinates _ _ (fun q hq ↦ ?_) hp
    rw [frozenForward_eq_origin T Q hP hr har hcarrier
      (frozenInputDomain_mono hrr haa (frozenSymbolInverse_maps T Q hηb hr' hInv' htrans' hq))]
    exact transportAveragedGradient_symbolInverse T Q hηb hr' hInv' htrans' hq
  rw [hright] at hleft
  exact congrArg (fun q : InputVariables n ↦ (q.2.1.1, q.2.2)) hleft

end Geometry

section Density

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (measurement : Euclidean n → ℝ) (high : ℝ → ℝ)
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a r' a' : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (hr' : 0 < r') (ha' : 0 < a')
    (hrr : r' ≤ r) (haa : a' ≤ a) (har : 6 * a ≤ 3 * r) (har' : 6 * a' ≤ 3 * r')
    {c C : ℝ} (hP : P.IsValid c C)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    {b cJ b' cJ' : ℝ} {V L V' L' : Set (ℝ × Euclidean (n - 1))}
    {G G' : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ (6 * a),
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)
    (hInv' : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a'))
      (dataBox z₀ ηb r') (dataSet z₀ ηb (2 * r')) (dataBox z₀ ηb (2 * r')) V' L' b' cJ' G')
    (htrans' : ∀ p ∈ physicalParameterSet z₀ (6 * a'),
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r' (angularWidth ηb r'),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r' / 4) * ‖u.2‖)

local notation "angular₀" => angularMask z₀ (NormedSpace.normalize ηb) ha'
  (And.left (angularWidth_spec hηb hr'))
local notation "d₀" => ({ uncutFrozenCoefficients T Q F row col Φ Y initial angular₀ high with
  measurement := measurement } : Coefficients n N)
local notation "J₀" => transportAbsoluteJacobian (adaptedSliceCoordinates T)
  (normalizedTransportPosition T Q 0)
local notation "u₀" => frozenSymbolInverse T Q z₀ ηb r (6 * a)
local notation "Ω₀" => frozenSymbolDomain T Q z₀ ηb r (6 * a)
local notation "u₁" => frozenSymbolInverse T Q z₀ ηb r' (6 * a')
local notation "Ω₁" => frozenSymbolDomain T Q z₀ ηb r' (6 * a')

include hr hrr haa har har' hP hcarrier hInv htrans hInv' htrans'

/-- The original smaller masks give exactly the same zero-extended density
with either constructed inverse. This holds for arbitrary measurement and
high-frequency masks, hence also for every radial regularization.
Consumer: matching the refined supported-shell realization to
`canonicalFrozenCarrierSymbol` (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem frozenExtendedDensity_eq_of_enlargement (p : Variables n × Euclidean 2) :
    extendedDensity d₀ J₀ u₀ Ω₀ p = extendedDensity d₀ J₀ u₁ Ω₁ p := by
  have haa₆ : 6 * a' ≤ 6 * a := mul_le_mul_of_nonneg_left haa (by norm_num)
  by_cases hp : p ∈ Ω₁
  · have hp' := frozenSymbolDomain_mono T Q hrr haa₆ hp
    rw [extendedDensity, indicator_of_mem hp', extendedDensity, indicator_of_mem hp]
    have he := frozenSymbolInverse_eq_of_enlargement T Q hrr haa₆ hP hηb hr hr'
      har hcarrier hInv htrans hInv' htrans' hp
    simp only [inverseCoordinates, he]
  · rw [extendedDensity, extendedDensity, indicator_of_notMem hp]
    by_cases hp' : p ∈ Ω₀
    · rw [indicator_of_mem hp']
      let q := inverseCoordinates u₀ p
      have hq := frozenSymbolInverse_maps T Q hηb hr hInv htrans hp'
      have hqne : q.2.2 ≠ 0 := hq.2.2.1
      have hm : angular₀ q.2.1 (‖q.2.2‖⁻¹ • q.2.2) = 0 := by
        by_contra hm
        have hqin := canonicalAngularMask_mem_frozenInputDomain z₀ hηb hr' ha'
          (by linarith) hqne hm
        have hcarrier' : closedBall (spectatorCenter z₀) (3 * r') ×ˢ
            closedBall (z₀ 0) (3 * r') ⊆
            carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2) :=
          (prod_mono (closedBall_subset_closedBall (by linarith))
            (closedBall_subset_closedBall (by linarith))).trans hcarrier
        apply hp
        rw [frozenSymbolDomain_eq_image T Q hP hηb hr' har' hcarrier' hInv' htrans']
        exact ⟨q, hqin, augmentedFrozenGradient_inverse T Q hP hηb hr har hcarrier
          hInv htrans hp'⟩
      change inputDensity d₀ J₀ q = 0
      simp only [inputDensity, inputWeight, uncutFrozenCoefficients, hm,
        zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, zero_div, zero_smul]
    · exact indicator_of_notMem hp' _

/-- The same original Lebesgue spectator integral is unchanged by enlargement
of the inverse domain. The smaller physical and angular masks are retained
literally (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem frozenAmplitude_eq_of_enlargement (S : Set (Euclidean 2)) (p : Variables n) :
    amplitude d₀ J₀ u₀ Ω₀ S p = amplitude d₀ J₀ u₁ Ω₁ S p := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v ↦ frozenExtendedDensity_eq_of_enlargement
    T Q F row col Φ Y initial measurement high hηb hr hr' ha' hrr haa har har' hP hcarrier
      hInv htrans hInv' htrans' (p, v)

omit measurement high in
/-- Exact reconciliation of the outer-inverse, smaller-mask expression with
the canonical frozen carrier symbol. Both reflections, their factor four,
and the original spectator ball are unchanged (`bg-real-symbol`). -/
theorem frozenCarrierSymbol_eq_canonical_of_enlargement (k : Euclidean n) :
    frozenCarrierSymbol T Q F row col Φ Y initial angular₀ FixedCutoffs.highFrequency
      (adaptedSliceCoordinates T) u₀ Ω₀ (closedBall (spectatorCenter z₀) (a' / 2)) k =
      canonicalFrozenCarrierSymbol T Q F row col Φ Y initial z₀ hηb hr' ha' k := by
  have he (p : Variables n) := frozenAmplitude_eq_of_enlargement
    T Q F row col Φ Y initial (fun _ ↦ 1) FixedCutoffs.highFrequency hηb hr hr' ha'
      hrr haa har har' hP hcarrier hInv htrans hInv' htrans'
      (closedBall (spectatorCenter z₀) (a' / 2)) p
  simp only [canonicalFrozenCarrierSymbol, frozenCarrierSymbol, TransportKernel.reflectedSymbolAmplitude]
  exact congrArg (fun m : Matrix (Fin n) (Fin n) ℝ ↦ (2 * (2 * Real.pi) ^ n) • m)
    (congrArg₂ (· + ·) (he (0, 0, k)) (he (0, 0, -k)))

omit measurement high in
/-- The literal measured zero-scale carrier, realized with the retained
outer inverse, has exactly the canonical smaller-mask full amplitude.
Both physical measurement factors, reflection and `k = 2πξ` are retained.
Consumer: `realQuadratureAdjoint_norm_sq_eq_euclideanFrozenEnergy`
(`new:lem:scaling`, `app:ch_background:eq:bg-real-symbol`). -/
theorem frozenMeasured_fullReflectedMatrixAmplitude_eq_canonical_of_enlargement
    (hcell : 4 * a' < 1 / 2) (x y ξ : Euclidean n) :
    CarrierNormalRealization.fullReflectedMatrixAmplitude
      (TransportKernel.coefficientsOfCarrier
        (normalizedCarrierData T Q F row col Φ Y initial ha' hcell angular₀
          FixedCutoffs.highFrequency 0) (FixedCutoffs.physical ha' 1))
      J₀ u₀ Ω₀ (closedBall (spectatorCenter z₀) (a' / 2)) ξ
      (AmplitudeBound.pairedPosition x y) =
      (FixedCutoffs.physical ha' 1 x * FixedCutoffs.physical ha' 1 y) •
        (fun i j ↦ (canonicalFrozenCarrierSymbol T Q F row col Φ Y initial z₀ hηb hr' ha'
          ((2 * Real.pi) • ξ) i j : ℂ)) := by
  rw [fullReflectedMatrixAmplitude_normalizedCarrierData_zero T Q F row col Φ Y initial
    angular₀ FixedCutoffs.highFrequency (adaptedSliceCoordinates T) hP hηb hr har hcarrier
      hInv htrans ha' hcell (closedBall (spectatorCenter z₀) (a' / 2)) x y ξ]
  rw [frozenCarrierSymbol_eq_canonical_of_enlargement T Q F row col Φ Y initial
    hηb hr hr' ha' hrr haa har har' hP hcarrier hInv htrans hInv' htrans']

omit measurement high in
/-- Equality of the complete measured reflected amplitudes for the retained
outer inverse and the constructed smaller canonical inverse. This function
identity transports smoothness, derivative bounds and the global PDO normal
without changing either measurement factor, the spectator ball, reflection,
or `k = 2πξ` (`new:lem:scaling`, `app:ch_background:eq:bg-real-symbol`). -/
theorem frozenMeasured_fullReflectedMatrixAmplitude_eq_of_enlargement
    (hcell : 4 * a' < 1 / 2) :
    CarrierNormalRealization.fullReflectedMatrixAmplitude
      (TransportKernel.coefficientsOfCarrier
        (normalizedCarrierData T Q F row col Φ Y initial ha' hcell angular₀
          FixedCutoffs.highFrequency 0) (FixedCutoffs.physical ha' 1))
      J₀ u₀ Ω₀ (closedBall (spectatorCenter z₀) (a' / 2)) =
    CarrierNormalRealization.fullReflectedMatrixAmplitude
      (TransportKernel.coefficientsOfCarrier
        (normalizedCarrierData T Q F row col Φ Y initial ha' hcell angular₀
          FixedCutoffs.highFrequency 0) (FixedCutoffs.physical ha' 1))
      J₀ u₁ Ω₁ (closedBall (spectatorCenter z₀) (a' / 2)) := by
  funext ξ z i j
  simp only [coefficientsOfCarrier_normalizedCarrierData_zero,
    CarrierNormalRealization.fullReflectedMatrixAmplitude,
    TransportKernel.reflectedSymbolAmplitude,
    frozenAmplitude_eq_of_enlargement T Q F row col Φ Y initial
      (FixedCutoffs.physical ha' 1) FixedCutoffs.highFrequency
      hηb hr hr' ha' hrr haa har har' hP hcarrier hInv htrans hInv' htrans']

end Density

end JanetCartan.ContinuumNormal.FrozenModel
