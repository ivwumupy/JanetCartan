module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.DensityLimitBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Regularity.Coefficients

/-!
# Literal frozen-density amplitude matching

Identify the origin multiplier in the normalized zero-limit bounds with the
existing frozen carrier's original initial scalar. The actual seed's time-zero
inverse label is retained, and the equality passes through the complete
spectator integral and reflected normalization on the same inverse domain.
The divided-footpoint source limit remains a different amplitude.

Consumer: normalized coercivity's spatial comparison with the frozen gap.
Sources: app:ch_background:prop:bg-normalized, bg-Nsigma,
app:ch_background:eq:bg-full-complex-amplitude, and bg-real-symbol.
-/

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalCarrier FrozenModel
open NullTransport ActualFlow FlowAmplitude
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
open CarrierVariation.FamilyInputs.PositiveReference

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)

/-- The original initial multiplier at normalized scale zero is evaluated
at the retained seed's time-zero inverse label. This coefficient identity
preserves every mask and the literal detector. Consumer: matching the frozen
branch of exists_sourceDensityLimit_reflected_bounds with the realized
NormalizedFrozenGap row (app:ch_background:eq:bg-Nsigma,
bg-full-complex-amplitude). -/
theorem normalized_zero_coefficients_initial_factor
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ) :
    let a := coefficientsOfCarrier
      (normalizedCarrierData T Q₀ F row col Φ Y (fun _ ↦ 1) hr hcell angular high 0)
      (FixedCutoffs.physical hr 1)
    coefficientsOfCarrier
      (normalizedCarrierData T Q₀ F row col Φ Y initial hr hcell angular high 0)
      (FixedCutoffs.physical hr 1) =
      {a with normal := fun p ↦ initial (Y (0, (0, parameter p.2))) • a.normal p} := by
  dsimp only
  rw [coefficientsOfCarrier_normalizedCarrierData_zero,
    coefficientsOfCarrier_normalizedCarrierData_zero]
  dsimp only [uncutFrozenCoefficients]
  congr 1
  funext p
  exact frozenSeedNormal_initial_factor T Q₀ F row col Φ Y initial p.2

/-- The origin-weighted full amplitude in the spatial-freezing estimate is
exactly the normalized frozen carrier with its original square-root initial
scalar. The time-zero inverse identity is derived from the supplied source
footpoint identities. The equality is proved through spectator integration
on the full given inverse domain, without equating it with the divided-label
limit. Consumer: the frozen normal realization in normalized coercivity
(app:ch_background:prop:bg-frame, bg-Nsigma, bg-real-symbol). -/
theorem fullReflectedMatrixAmplitude_frozenDensity_eq_normalizedZero
    {V : Set CarrierParameter}
    (hzero : ∀ z ∈ V, (densityFootpoint T Y (0, z)).1 = 0)
    (hparam : ∀ z ∈ V, (densityFootpoint T Y (0, z)).2 = parameter z)
    (J : InputVariables n → ℝ) (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    (hlabel : ∀ p ∈ Ω, (inverseCoordinates u p).2.1 ∈ V)
    (v : Euclidean (n - 1) × Euclidean 3 → ℝ) :
    let a := coefficientsOfCarrier
      (normalizedCarrierData T Q₀ F row col Φ Y (fun _ ↦ 1) hr hcell angular high 0)
      (FixedCutoffs.physical hr 1)
    fullReflectedMatrixAmplitude
      {a with normal := fun p ↦ Real.sqrt (1 + v (0, parameter p.2)) • a.normal p}
      J u Ω S =
      fullReflectedMatrixAmplitude
        (coefficientsOfCarrier
          (normalizedCarrierData T Q₀ F row col Φ Y (fun q ↦ Real.sqrt (1 + v q))
            hr hcell angular high 0) (FixedCutoffs.physical hr 1)) J u Ω S := by
  intro a
  rw [normalized_zero_coefficients_initial_factor]
  have hinit (z : CarrierParameter) (hz : z ∈ V) : Y (0, (0, parameter z)) = (0, parameter z) := by
    have he : densityFootpoint T Y (0, z) = (0, parameter z) :=
      Prod.ext (hzero z hz) (hparam z hz)
    simpa [densityFootpoint_eq, coordinates_apply, adaptedCoordinates_apply] using he
  let ao : Coefficients n N :=
    {a with normal := fun p ↦ Real.sqrt (1 + v (0, parameter p.2)) • a.normal p}
  let af : Coefficients n N :=
    {a with normal := fun p ↦ Real.sqrt (1 + v (Y (0, (0, parameter p.2)))) • a.normal p}
  have hext : extendedDensity ao J u Ω = extendedDensity af J u Ω := by
    funext p
    by_cases hp : p ∈ Ω
    · simp only [extendedDensity, indicator_of_mem hp, inputDensity, inputWeight,
        ao, af, inverseCoordinates]
      have hi := hinit _ (hlabel p hp)
      change Y (0, (0, parameter ((u p).1, p.2))) = (0, parameter ((u p).1, p.2)) at hi
      rw [hi]
    · simp only [extendedDensity, indicator_of_notMem hp]
  have hamp : amplitude ao J u Ω S = amplitude af J u Ω S := by
    funext p
    exact integral_congr_ae (Filter.Eventually.of_forall (fun z ↦ congrFun hext (p, z)))
  change fullReflectedMatrixAmplitude ao J u Ω S = fullReflectedMatrixAmplitude af J u Ω S
  funext ξ z
  ext i j
  simp only [fullReflectedMatrixAmplitude, reflectedSymbolAmplitude, hamp]

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
