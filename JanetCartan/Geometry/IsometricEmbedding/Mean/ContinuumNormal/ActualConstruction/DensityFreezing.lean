module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.SpatialFreezing
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.DensityLimit

/-!
# Spatial comparison of the actual density limit and frozen-label normal

The two density limits differ away from the spatial origin, as checked in
`DensityLimit`. At the origin they agree exactly. Apply the constructed
full-amplitude spatial-freezing estimate to their literal reflected difference.
The resulting `C A r` error uses a uniform finite bound, not a small density or
an assumed operator-continuity conclusion. The same geometric coefficients,
inverse, Jacobian, masks and spectator measure occur on both sides.

Consumers: the initialized local lower bound and normalized `SourceInverse`.
The actual common family, uniform primitive bounds, carrier realizations and
subsequent gap absorption still have to be instantiated. This file does not
assert the actual local or global coercivity theorem.
Sources: `app:ch_background:prop:bg-frame`, `bg-full-complex-amplitude`, `bg-Nsigma`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Set Filter
open scoped ContDiff Topology InnerProductSpace NNReal Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.ActualConstruction
open Pseudodifferential AmplitudeBound
variable {n : ℕ}
local notation "E" => Euclidean n
local notation "P" => Euclidean (2 * n)

open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalCarrier
open CarrierVariation.FamilyInputs.WideDensity
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization

/-- At the spatial origin the actual divided ODE label agrees with the
frozen label. This is an origin identity only; away from the origin the two
labels need not agree (`app:ch_background:eq:bg-Nsigma`, `bg-frame`). -/
theorem sourceDensityFootpointExtension_zero_at_origin
    {P₀ : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P₀ U hU)
    (Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (z : CarrierParameter) :
    sourceDensityFootpointExtension T Y (0, (0, z)) = (0, parameter z) := by
  rw [sourceDensityFootpointExtension_zero_eq_differential]
  apply Prod.ext
  · ext j
    simp
  · rfl

/-- The two actual zero-scale density factors give the frozen label square
at the spatial origin. No restriction to constant initial densities is used
(`app:ch_background:eq:bg-full-complex-amplitude`, `bg-Nsigma`). -/
theorem sourceDensityPairLimit_at_origin
    {P₀ : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P₀ U hU)
    (Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (v : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (z : CarrierParameter) (η : Euclidean (n - 1)) :
    sourceDensityPairLimit T v Y ((0, 0), z, η) = (1 + v (0, parameter z)) ^ 2 := by
  simp only [sourceDensityPairLimit, densityPair, densityEndpoint, Bool.false_eq_true,
    ↓reduceIte, sourceDensityFootpointExtension_zero_at_origin, pow_two]

/-- Instantiate the spatial-freezing origin condition for the LITERAL
transported-density limit and frozen-label full amplitudes. The same base
coefficients, inverse, Jacobian, masks, spectator set and reflected Fourier
normalization occur on both sides. No equality away from the origin is asserted
(`app:ch_background:eq:bg-full-complex-amplitude`, `bg-real-symbol`, `bg-Nsigma`). -/
theorem fullReflectedMatrixAmplitude_sourceDensityLimit_sub_frozen_zero
    {P₀ : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P₀ U hU)
    (Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (v : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {N : ℕ} (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (S : Set (Euclidean 2)) :
    let aActual := {a with
      normal := fun q ↦ Real.sqrt (1 + v (sourceDensityFootpointExtension T Y (0, q))) • a.normal q}
    let aFrozen := {a with
      normal := fun q ↦ Real.sqrt (1 + v (0, parameter q.2)) • a.normal q}
    ∀ ξ, (fullReflectedMatrixAmplitude aActual J u Ω S -
      fullReflectedMatrixAmplitude aFrozen J u Ω S) ξ 0 = 0 := by
  dsimp only
  let aActual := {a with
    normal := fun q ↦ Real.sqrt (1 + v (sourceDensityFootpointExtension T Y (0, q))) • a.normal q}
  let aFrozen := {a with
    normal := fun q ↦ Real.sqrt (1 + v (0, parameter q.2)) • a.normal q}
  have hi (z : CarrierParameter) (η : Euclidean (n - 1)) :
      inputDensity aActual J ((0, 0), z, η) = inputDensity aFrozen J ((0, 0), z, η) := by
    simp only [inputDensity, inputWeight, aActual, aFrozen,
      sourceDensityFootpointExtension_zero_at_origin]
  have ha (k : E) : amplitude aActual J u Ω S (0, 0, k) =
      amplitude aFrozen J u Ω S (0, 0, k) := by
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hz : ((0, 0, k), z) ∈ Ω
    · simp only [extendedDensity, indicator_of_mem hz, inverseCoordinates]
      exact hi _ _
    · simp only [extendedDensity, indicator_of_notMem hz]
  intro ξ
  change fullReflectedMatrixAmplitude aActual J u Ω S ξ 0 -
    fullReflectedMatrixAmplitude aFrozen J u Ω S ξ 0 = 0
  apply sub_eq_zero.mpr
  ext i j
  simp only [fullReflectedMatrixAmplitude, map_zero, reflectedSymbolAmplitude,
    ha]

open ContinuumRow PeriodicLocalL2 in
/-- The actual divided-footpoint weighted limit and the frozen-label normal
differ by at most `C * (AActual + AFrozen) * r * ‖w‖²` on small support.
The constant precedes the density and both finite derivative budgets. The
origin equality, difference budget, measurement support, PDO subtraction and
real transfer are all discharged on these literal amplitudes. Neither the
initial density nor its original allowed interval is made smaller.

Consumers: the initialized local gap and the uniform `SourceInverse` gap.
`both-normalized-selection`, `both-normalized-baseline` and
`both-normalized-normal-limit` must still supply the SAME unit zero slice,
its density-uniform primitive bounds and actual carrier-normal realizations.
This comparison is checked progress, not an instantiated coercivity theorem.
Sources: `app:ch_background:prop:bg-frame`, Steps 2–3; `bg-local-bound`, `bg-Nsigma`. -/
theorem exists_sourceDensityLimit_frozen_error_constant
    (hn : 0 < n) (R : ℝ) (θ : P → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hθs : HasCompactSupport θ) (hθbox : ∀ z, θ z ≠ 0 → ∀ j, |z j| ≤ R)
    (χ : E → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ)
    (hχθ : ∀ x y, θ (pairedPosition x y) ≠ 0 → χ x = 1 ∧ χ y = 1) :
    ∃ C > 0, ∀ {P₀ : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
      (T : PatchQuantitativeFamily P₀ U hU)
      (Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
      (v : Euclidean (n - 1) × Euclidean 3 → ℝ)
      {N : ℕ} (a : Coefficients n N) (J : InputVariables n → ℝ)
      (u : Variables n × Euclidean 2 → SliceVariable n)
      (Ω : Set (Variables n × Euclidean 2)) (S : Set (Euclidean 2))
      (hsupport : ∀ x, a.measurement x ≠ 0 → ∀ j, |x j| ≤ R),
      (∀ z, a.measurement (freezingOutputProjection z) ≠ 0 →
        a.measurement (freezingSourceProjection z) ≠ 0 → θ z = 1) →
      let aActual := {a with
        normal := fun q ↦ Real.sqrt (1 + v (sourceDensityFootpointExtension T Y (0, q))) • a.normal q}
      let aFrozen := {a with
        normal := fun q ↦ Real.sqrt (1 + v (0, parameter q.2)) • a.normal q}
      let bActual := fullReflectedMatrixAmplitude aActual J u Ω S
      let bFrozen := fullReflectedMatrixAmplitude aFrozen J u Ω S
      ∀ (hbActual : ContDiff ℝ ∞ (Function.uncurry bActual))
        (hbFrozen : ContDiff ℝ ∞ (Function.uncurry bFrozen)) (AActual AFrozen : ℝ≥0)
        (hActual : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ bActual ξ z i j)
          (2 * (n + 1) + 1) AActual)
        (hFrozen : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ bFrozen ξ z i j)
          (2 * (n + 1) + 1) AFrozen),
      let NActual := realOutputCompression (transferOperator
        (vectorTwoPositionL2Operator hn R bActual hbActual
          (fullReflectedMatrixAmplitude_supportedInCenteredBox aActual J u Ω S R hsupport)
          AActual (fun i j ξ is his ↦ hActual i j ξ is (by omega))))
      let NFrozen := realOutputCompression (transferOperator
        (vectorTwoPositionL2Operator hn R bFrozen hbFrozen
          (fullReflectedMatrixAmplitude_supportedInCenteredBox aFrozen J u Ω S R hsupport)
          AFrozen (fun i j ξ is his ↦ hFrozen i j ξ is (by omega))))
      ∀ r : ℝ, 0 ≤ r → (∀ x ∈ Metric.closedBall (0 : E) r, χ x = 1) →
      ∀ w : OutputL2 n,
      (∀ᵐ x ∂volume, x ∉ torusChart (Metric.closedBall (0 : E) r) → w x = 0) →
      |inner ℝ ((NActual - NFrozen) w) w| ≤ C * (AActual + AFrozen) * r * ‖w‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_real_fullAmplitude_small_support_constant
    hn R θ hθ hθs hθbox χ hχ hχs hχθ
  refine ⟨C, hC, ?_⟩
  intro P₀ U hU T Y v N a J u Ω S hsupport hθa
  dsimp only
  let aActual := {a with
    normal := fun q ↦ Real.sqrt (1 + v (sourceDensityFootpointExtension T Y (0, q))) • a.normal q}
  let aFrozen := {a with
    normal := fun q ↦ Real.sqrt (1 + v (0, parameter q.2)) • a.normal q}
  let bActual := fullReflectedMatrixAmplitude aActual J u Ω S
  let bFrozen := fullReflectedMatrixAmplitude aFrozen J u Ω S
  intro hbActual hbFrozen AActual AFrozen hActual hFrozen
  let hsActual := fullReflectedMatrixAmplitude_supportedInCenteredBox aActual J u Ω S R hsupport
  let hsFrozen := fullReflectedMatrixAmplitude_supportedInCenteredBox aFrozen J u Ω S R hsupport
  have hsDiff : ∀ ξ i j, SupportedInCenteredBox R
      (fun z ↦ (bActual - bFrozen) ξ z i j) := by
    intro ξ i j z hz
    by_cases ha : bActual ξ z i j = 0
    · apply hsFrozen ξ i j z
      simpa only [Pi.sub_apply, Matrix.sub_apply, ha, zero_sub, neg_ne_zero] using hz
    · exact hsActual ξ i j z ha
  have hDiff : ∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ (bActual - bFrozen) ξ z i j) (2 * (n + 1) + 1)
        (AActual + AFrozen : ℝ≥0) := by
    intro i j ξ is his z
    have ha : ContDiff ℝ ∞ (fun z ↦ bActual ξ z i j) :=
      ((matrixEntryEvaluation i j).contDiff.comp hbActual).comp
        (contDiff_const.prodMk contDiff_id)
    have hf : ContDiff ℝ ∞ (fun z ↦ bFrozen ξ z i j) :=
      ((matrixEntryEvaluation i j).contDiff.comp hbFrozen).comp
        (contDiff_const.prodMk contDiff_id)
    change ‖euclideanCoordinateDerivList is
      (fun z ↦ bActual ξ z i j - bFrozen ξ z i j) z‖ ≤ (AActual : ℝ) + AFrozen
    have he : (fun z ↦ bActual ξ z i j - bFrozen ξ z i j) =
        (fun z ↦ bActual ξ z i j + (-1 : ℂ) * bFrozen ξ z i j) := by
      funext z
      simp only [neg_one_mul, sub_eq_add_neg]
    rw [he, euclideanCoordinateDerivList_add ha (contDiff_const.mul hf),
      euclideanCoordinateDerivList_const_mul hf]
    simpa only [neg_one_mul, sub_eq_add_neg] using
      (norm_sub_le (euclideanCoordinateDerivList is (fun z ↦ bActual ξ z i j) z)
        (euclideanCoordinateDerivList is (fun z ↦ bFrozen ξ z i j) z)).trans
          (add_le_add (hActual i j ξ is his z) (hFrozen i j ξ is his z))
  have hmask : ∀ ξ z, (bActual - bFrozen) ξ z ≠ 0 → θ z = 1 := by
    intro ξ z hz
    apply hθa z
    · intro hm
      apply hz
      ext i j
      simp [bActual, bFrozen, fullReflectedMatrixAmplitude,
        TestChartTransfer.reflectedAmplitude_eq_zero_of_output_measurement
          aActual J u Ω S _ _ _ hm,
        TestChartTransfer.reflectedAmplitude_eq_zero_of_output_measurement
          aFrozen J u Ω S _ _ _ hm]
    · intro hm
      apply hz
      ext i j
      simp [bActual, bFrozen, fullReflectedMatrixAmplitude,
        TestChartTransfer.reflectedAmplitude_eq_zero_of_source_measurement
          aActual J u Ω S _ _ _ hm,
        TestChartTransfer.reflectedAmplitude_eq_zero_of_source_measurement
          aFrozen J u Ω S _ _ _ hm]
  intro r hr hplateau w hw
  have hh := hbound (bActual - bFrozen) (hbActual.sub hbFrozen) hsDiff
    (AActual + AFrozen) hDiff
    (fullReflectedMatrixAmplitude_sourceDensityLimit_sub_frozen_zero T Y v a J u Ω S)
    hmask r hr hplateau w hw
  simp only [NNReal.coe_add] at hh
  erw [CarrierVariation.vectorTwoPositionL2Operator_sub hn R bActual bFrozen
    hbActual hbFrozen (hbActual.sub hbFrozen) hsActual hsFrozen hsDiff
    AActual AFrozen (AActual + AFrozen)
    (fun i j ξ is his ↦ hActual i j ξ is (by omega))
    (fun i j ξ is his ↦ hFrozen i j ξ is (by omega))
    (fun i j ξ is his ↦ hDiff i j ξ is (by omega)),
    CarrierVariation.transferOperator_sub, realOutputCompression_sub] at hh
  exact hh

end JanetCartan.ContinuumNormal.ActualConstruction
