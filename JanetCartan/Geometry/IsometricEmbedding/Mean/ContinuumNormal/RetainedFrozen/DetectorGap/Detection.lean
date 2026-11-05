module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.DetectorGap.Regularity

/-!
# Zero-energy detection for the retained frozen masks

A positive literal weight at an interior spectator point forces zero-energy
vectors to annihilate that root detector. Reflection and the factor four are
preserved. `retainedFrozenMatrixSymbol_unit_pos_of_incidence` supplies the
proved primitive regularity and integrability; the supplied-family assembly
proves the positive weight from the selected null column
(`app:ch_background:prop:bg-frame`, Step 2).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter MeasureTheory Matrix
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.RetainedFrozen
open FrozenModel ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic
open ContinuumNormalReduction TransportSymbol ConicChart TransportKernel

private def matrixTest {n : ℕ} (s : Euclidean n) : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
  (show Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ from
    { toFun := fun M ↦ dotProduct (fun i ↦ s i) (M *ᵥ (fun i ↦ s i))
      map_add' := by intro A B; simp [Matrix.add_mulVec, dotProduct_add]
      map_smul' := by intro c A; simp [Matrix.smul_mulVec, dotProduct_smul] }).toContinuousLinearMap

private theorem matrixTest_apply {n : ℕ} (s : Euclidean n) (M : Matrix (Fin n) (Fin n) ℝ) :
    matrixTest s M = dotProduct (fun i ↦ s i) (M *ᵥ (fun i ↦ s i)) := rfl

private theorem matrixTest_rankOne {n : ℕ} (s q : Euclidean n) (w : ℝ) :
    matrixTest s (w • Matrix.vecMulVec (fun i ↦ q i) (fun i ↦ q i)) = w * ⟪q, s⟫_ℝ ^ 2 := by
  rw [map_smul, matrixTest_apply]
  simp only [Matrix.vecMulVec_mulVec, dotProduct_smul, smul_eq_mul,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial, op_smul_eq_mul]
  rw [dotProduct_comm (fun i ↦ s i) (fun i ↦ q i)]
  ring

section Carrier
variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (z₀ : Euclidean 3) {ηb : Euclidean (n - 1)} {r a r' a' : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (hr' : 0 < r') (ha' : 0 < a')

local notation "angular₀" => angularMask z₀ (NormedSpace.normalize ηb) ha'
  (And.left (angularWidth_spec hηb hr'))
local notation "a₀" => uncutFrozenCoefficients T Q F row col Φ Y initial angular₀
  FixedCutoffs.highFrequency
local notation "J₀" => transportAbsoluteJacobian (adaptedSliceCoordinates T)
  (normalizedTransportPosition T Q 0)
local notation "u₀" => frozenSymbolInverse T Q z₀ ηb r (6 * a)
local notation "Ω₀" => frozenSymbolDomain T Q z₀ ηb r (6 * a)
local notation "S₀" => closedBall (spectatorCenter z₀) (a' / 2)

private theorem canonicalDensity_test_nonneg (k : Euclidean n) (s : Euclidean n)
    (v : Euclidean 2) : 0 ≤ matrixTest s (extendedDensity a₀ J₀ u₀ Ω₀ ((0, 0, k), v)) := by
  by_cases hp : ((0, 0, k), v) ∈ Ω₀
  · rw [extendedDensity, indicator_of_mem hp, matrixTest_apply]
    simpa only [star_trivial] using
      (frozenInputDensity_posSemidef T Q F row col Φ Y initial angular₀
        FixedCutoffs.highFrequency (adaptedSliceCoordinates T) (inverseCoordinates u₀ ((0, 0, k), v))).dotProduct_mulVec_nonneg
        (fun i ↦ s i)
  · simp only [extendedDensity, indicator_of_notMem hp, map_zero, le_refl]

private theorem canonicalAmplitude_test_nonneg (k : Euclidean n) (s : Euclidean n) :
    0 ≤ matrixTest s (amplitude a₀ J₀ u₀ Ω₀ S₀ (0, 0, k)) := by
  by_cases hint : Integrable (fun v ↦ extendedDensity a₀ J₀ u₀ Ω₀ ((0, 0, k), v))
      (volume.restrict S₀)
  · rw [amplitude, ← (matrixTest s).integral_comp_comm hint]
    exact integral_nonneg (canonicalDensity_test_nonneg T Q F row col Φ Y initial z₀ hηb hr' ha' k s)
  · simp only [amplitude, integral_undef hint, map_zero, le_refl]

include hr in
/-- Zero energy annihilates the actual root detector. The consumer
`retainedFrozenMatrixSymbol_unit_pos_of_incidence` discharges `hreg` and `hint`
using `retainedFrozenPrimitiveRegularity_unit` and
`retainedFrozenExtendedDensity_unit_integrable`. The root, inverse identity
and positive weight are produced by `retained_cube_incidence_positive_weight`
without altering the masks (`app:ch_background:prop:bg-frame`). -/
theorem retainedFrozenCarrierSymbol_detector_eq_zero_of_integrable
    {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ (6 * a),
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)
    (hV : IsOpen V) (hLV : L ⊆ V)
    (hreg : PrimitiveRegularity a₀ J₀ (frozenInputDomain z₀ ηb r (6 * a)))
    {k : Euclidean n} {z : Euclidean 3}
    (hint : Integrable (fun v ↦ extendedDensity a₀ J₀ u₀ Ω₀ ((0, 0, k), v))
      (volume.restrict S₀))
    (hp : ((0, 0, k), spectatorCenter z₀) ∈ Ω₀)
    (hz : parameter ((u₀ ((0, 0, k), spectatorCenter z₀)).1, spectatorCenter z₀) = z)
    (hw : 0 < inputWeight a₀ J₀ (inverseCoordinates u₀ ((0, 0, k), spectatorCenter z₀)))
    (s : Euclidean n)
    (hzero : dotProduct (fun i ↦ s i)
      (retainedFrozenCarrierSymbol T Q F row col Φ Y initial z₀ r a hηb hr' ha' k *ᵥ (fun i ↦ s i)) = 0) :
    ⟪quadratic (Q.1 0) (T.carrierGradient Q 0 z), s⟫_ℝ = 0 := by
  let density : Euclidean 2 → Matrix (Fin n) (Fin n) ℝ :=
    fun v ↦ extendedDensity a₀ J₀ u₀ Ω₀ ((0, 0, k), v)
  let f : Euclidean 2 → ℝ := fun v ↦ matrixTest s (density v)
  have hfint : Integrable f (volume.restrict S₀) := (matrixTest s).integrable_comp hint
  have hfnonneg : ∀ v, 0 ≤ f v :=
    canonicalDensity_test_nonneg T Q F row col Φ Y initial z₀ hηb hr' ha' k s
  have hnegative := canonicalAmplitude_test_nonneg T Q F row col Φ Y initial z₀ (r := r) (a := a) hηb hr' ha' (-k) s
  have hreflect : (2 * (2 * Real.pi) ^ n) *
      ((∫ v in S₀, f v) + matrixTest s (amplitude a₀ J₀ u₀ Ω₀ S₀ (0, 0, -k))) = 0 := by
    change matrixTest s (retainedFrozenCarrierSymbol T Q F row col Φ Y initial z₀ r a hηb hr' ha' k) = 0 at hzero
    simpa only [retainedFrozenCarrierSymbol, frozenCarrierSymbol, reflectedSymbolAmplitude,
      map_smul, map_add, smul_eq_mul, amplitude, ← (matrixTest s).integral_comp_comm hint,
      f, density] using hzero
  have hsum := (mul_eq_zero.mp hreflect).resolve_left (by positivity)
  have hfzero : ∫ v in S₀, f v = 0 := le_antisymm (by linarith) (integral_nonneg hfnonneg)
  have hae : f =ᵐ[volume.restrict S₀] 0 :=
    (integral_eq_zero_iff_of_nonneg hfnonneg hfint).mp hfzero
  have hΩ := frozenSymbolDomain_open T Q hηb hr hInv htrans hV hLV
  have hu := frozenSymbolInverse_smooth T Q hηb hr hInv htrans hLV
  have hmap := frozenSymbolInverse_maps T Q hηb hr hInv htrans
  have hdensity : ContinuousOn (extendedDensity a₀ J₀ u₀ Ω₀) Ω₀ := by
    apply (((inputDensity_contDiffOn hreg).comp
      (inverseCoordinates_contDiffOn hu) hmap).continuousOn).congr
    intro p hp
    exact indicator_of_mem hp _
  let W : Set (Euclidean 2) := {v | ((0, 0, k), v) ∈ Ω₀} ∩ ball (spectatorCenter z₀) (a' / 2)
  have hWo : IsOpen W := by
    change IsOpen ((fun v : Euclidean 2 ↦ (((0 : Euclidean n), 0, k), v)) ⁻¹' Ω₀ ∩
      ball (spectatorCenter z₀) (a' / 2))
    exact (hΩ.preimage (continuous_const.prodMk continuous_id)).inter isOpen_ball
  have hWsub : W ⊆ S₀ := fun _ hv ↦ ball_subset_closedBall hv.2
  have hfcont : ContinuousOn f W := (matrixTest s).continuous.comp_continuousOn
    (hdensity.comp (continuousOn_const.prodMk continuousOn_id) (fun _ hv ↦ hv.1))
  have hvW : spectatorCenter z₀ ∈ W := ⟨hp, mem_ball_self (by positivity)⟩
  have hvzero : f (spectatorCenter z₀) = 0 :=
    Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset hWsub hae)
      hWo hfcont continuousOn_const hvW
  change matrixTest s (extendedDensity a₀ J₀ u₀ Ω₀ ((0, 0, k), spectatorCenter z₀)) = 0 at hvzero
  rw [extendedDensity, indicator_of_mem hp] at hvzero
  change matrixTest s (inputWeight a₀ J₀ (inverseCoordinates u₀ ((0, 0, k), spectatorCenter z₀)) •
    Matrix.vecMulVec (quadratic (Q.1 0) (T.carrierGradient Q 0
      (parameter ((u₀ ((0, 0, k), spectatorCenter z₀)).1, spectatorCenter z₀))))
      (quadratic (Q.1 0) (T.carrierGradient Q 0
        (parameter ((u₀ ((0, 0, k), spectatorCenter z₀)).1, spectatorCenter z₀))))) = 0 at hvzero
  rw [hz, matrixTest_rankOne] at hvzero
  exact (sq_eq_zero_iff).mp ((mul_eq_zero.mp hvzero).resolve_left hw.ne')

end Carrier
end JanetCartan.ContinuumNormal.RetainedFrozen
